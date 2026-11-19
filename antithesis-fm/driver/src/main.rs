//! The driver: an etcd-io/raft cluster of three or five nodes whose state
//! machine keeps a running sum of the integers clients add, restricted to the
//! features the TLA+ model covers (see spec/README.md).
//!
//! Besides checking client-visible behaviour, it collects
//! the steps the nodes report and runs the TLC stream check on them
//! (tracekit's trace.rs), and checks single-node properties on the same
//! steps (steps.rs).
//!
//! Rules send adds and reads to the nodes and record each outcome in the
//! model. The nodes' forwarded logs feed the model with what every node
//! applied, so each response and each node's history is checked against the
//! others as it arrives.

mod logs;
mod model;
#[path = "../../tracekit/driver/trace.rs"]
mod trace;
mod steps;

use antithesis_sdk::{assert_always, assert_reachable, assert_sometimes_greater_than};
use hegel::generators as gs;
use hegel::stateful::machine;
use hegel::TestCase;
use logs::Logs;
use model::{Model, Outcome, StateAt, StateSource};
use serde_json::{json, Value};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

/// The nodes' names: DRIVER_NODES, comma-separated, or raft1 to raft3.
static NODES: std::sync::LazyLock<Vec<String>> = std::sync::LazyLock::new(|| {
    std::env::var("DRIVER_NODES")
        .unwrap_or_else(|_| "raft1,raft2,raft3".into())
        .split(',')
        .map(String::from)
        .collect()
});
const EVENTUALLY_P: f64 = 0.0001;
/// TLC cannot follow a behaviour past 65,535 states, so the streaming check
/// dies at that many events. The eventually starts before that.
const TRACE_LIMIT: u64 = 55_000;
/// Operations per second across all workers. Every add and every
/// linearizable read is a log entry, and trace validation cost grows with the
/// number of steps, so the rates are low.
const DEFAULT_ADD_RATE: f64 = 5.0;
const DEFAULT_LINEAR_RATE: f64 = 2.0;
const DEFAULT_STALE_RATE: f64 = 5.0;
/// Requests to hand leadership over, per second (DRIVER_TRANSFER_RATE). Off
/// unless the run sets it.
const DEFAULT_TRANSFER_RATE: f64 = 0.0;
/// Changes of membership asked for, per second (DRIVER_CONF_RATE). Off unless
/// the run sets it.
const DEFAULT_CONF_RATE: f64 = 0.0;

/// A token bucket: `rate` tokens per second, holding at most one second's worth.
struct Bucket {
    rate: f64,
    state: Mutex<(f64, Instant)>,
}

impl Bucket {
    fn new(env: &str, default: f64) -> Self {
        let rate = std::env::var(env).ok().and_then(|v| v.parse().ok()).unwrap_or(default);
        Bucket { rate, state: Mutex::new((0.0, Instant::now())) }
    }

    /// Takes a token if there is one. Without one, waits briefly so idle
    /// workers do not spin.
    fn take(&self) -> bool {
        let got = {
            let mut b = self.state.lock().unwrap_or_else(|e| e.into_inner());
            let now = Instant::now();
            b.0 = (b.0 + now.duration_since(b.1).as_secs_f64() * self.rate).min(self.rate.max(1.0));
            b.1 = now;
            if b.0 >= 1.0 {
                b.0 -= 1.0;
                true
            } else {
                false
            }
        };
        if !got {
            std::thread::sleep(Duration::from_millis(20));
        }
        got
    }
}

fn log(msg: &str) {
    eprintln!("driver: {msg}");
}

enum Resp {
    Ok(Value),
    /// The server answered with an error body.
    Err(u16, Value),
    /// No answer: connection refused, reset or timed out.
    NoAnswer(String),
}

struct Client {
    agent: ureq::Agent,
    urls: Vec<String>,
}

impl Client {
    fn new() -> Self {
        let urls = std::env::var("NODE_URLS")
            .unwrap_or_else(|_| NODES.iter().map(|n| format!("http://{n}:8000")).collect::<Vec<_>>().join(","))
            .split(',')
            .map(String::from)
            .collect();
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_millis(500))
            .timeout(Duration::from_secs(3))
            .build();
        Client { agent, urls }
    }

    fn call(&self, node: usize, method: &str, path: &str) -> Resp {
        let url = format!("{}{}", self.urls[node], path);
        match self.agent.request(method, &url).call() {
            Ok(r) => match r.into_json::<Value>() {
                Ok(v) => Resp::Ok(v),
                Err(e) => Resp::NoAnswer(format!("bad body: {e}")),
            },
            Err(ureq::Error::Status(code, r)) => Resp::Err(code, r.into_json::<Value>().unwrap_or(Value::Null)),
            Err(e) => Resp::NoAnswer(e.to_string()),
        }
    }
}

fn node_index(name: &str) -> Option<usize> {
    NODES.iter().position(|n| *n == name)
}

fn state_from(v: &Value) -> Option<StateAt> {
    Some(StateAt {
        index: v["index"].as_u64()?,
        term: v["term"].as_u64()?,
        sum: v["sum"].as_i64()?,
        count: v["count"].as_u64()?,
        digest: v["digest"].as_str()?.parse().ok()?,
        node: v["node"].as_str()?.to_string(),
    })
}

struct Driver {
    client: Client,
    model: Arc<Mutex<Model>>,
    logs: Arc<Logs>,
    leader_hint: AtomicUsize,
    /// Every rule holds a read guard while it acts; the eventually takes the
    /// write guard, so it starts once in-flight requests finish.
    quiesce: RwLock<()>,
    eventually_lock: Mutex<()>,
    eventually_enabled: bool,
    trace: trace::Trace,
    add_bucket: Bucket,
    linear_bucket: Bucket,
    stale_bucket: Bucket,
    transfer_bucket: Bucket,
    conf_bucket: Bucket,
}

const CONF_ASKED: &str = "a leader is asked to change the membership";
const CONF_JOINT_ASKED: &str = "a leader is asked for a joint change of membership";
const CONF_LEAVE_ASKED: &str = "a leader in a joint configuration is asked to leave it";
const REUNITED: &str = "every node is a voter again once faults stop";
const FORWARDED: &str = "a write sent to a node that does not lead is acknowledged";
const TRANSFER_ASKED: &str = "a leader is asked to hand leadership to another node";

impl Driver {
    fn model(&self) -> std::sync::MutexGuard<'_, Model> {
        self.model.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn update_hint(&self, body: &Value) {
        if let Some(i) = body["leader"].as_str().and_then(node_index) {
            self.leader_hint.store(i, Ordering::Relaxed);
        }
    }

    /// Picks the node a leader-only request goes to: usually the believed
    /// leader, sometimes any node, so followers' redirects get exercised.
    fn pick_target(&self, tc: &TestCase) -> usize {
        if tc.draw(gs::weighted_booleans(0.8)) {
            self.leader_hint.load(Ordering::Relaxed)
        } else {
            tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1))
        }
    }

    /// Sends one add and records its outcome. Returns the leader hint from
    /// a not-leader response, if any.
    fn add_once(&self, node: usize, value: i64) -> (Outcome, Option<usize>) {
        let op = self.model().send(value);
        let resp = self.client.call(node, "POST", &format!("/add?op={op}&value={value}"));
        let (outcome, hint) = match &resp {
            Resp::Ok(v) => match (v["index"].as_u64(), v["sum"].as_i64()) {
                (Some(index), Some(sum)) => {
                    // Where followers pass writes on, the node that answered
                    // need not lead: it says who does.
                    match v["leader"].as_str().and_then(node_index) {
                        Some(leader) => {
                            self.leader_hint.store(leader, Ordering::Relaxed);
                            if leader != node {
                                steps::sometimes(FORWARDED, true, &json!({"node": NODES[node]}));
                            }
                        }
                        None => self.leader_hint.store(node, Ordering::Relaxed),
                    }
                    (Outcome::Acked { index, sum }, None)
                }
                _ => (Outcome::Unknown, None),
            },
            Resp::Err(_, b) if b["error"] == "not_leader" => {
                self.update_hint(b);
                (Outcome::Rejected, b["leader"].as_str().and_then(node_index))
            }
            Resp::Err(_, b) if b["error"] == "enqueue_timeout" => (Outcome::Rejected, None),
            Resp::Err(..) | Resp::NoAnswer(_) => (Outcome::Unknown, None),
        };
        if outcome == Outcome::Unknown {
            assert_reachable!(
                "a write's outcome is unknown to the client",
                &json!({"node": NODES[node], "op": op, "resp": match &resp {
                    Resp::Err(c, b) => json!({"code": c, "body": b}),
                    Resp::NoAnswer(e) => json!(e),
                    Resp::Ok(v) => v.clone(),
                }})
            );
        }
        self.model().complete(op, outcome, &NODES[node]);
        (outcome, hint)
    }

    fn most_lagging(&self) -> Option<usize> {
        let s = self.logs.states.lock().unwrap_or_else(|e| e.into_inner());
        s.nodes.iter().min_by_key(|(_, n)| n.applied).and_then(|(c, _)| node_index(c))
    }

    /// Retries a linearizable read, following not-leader hints, until one
    /// succeeds or the deadline passes.
    fn linear_read_until(&self, first: usize, deadline: Instant) -> Option<StateAt> {
        let mut target = first;
        let mut attempts = 0usize;
        while Instant::now() < deadline {
            attempts += 1;
            match self.client.call(target, "GET", "/sum") {
                Resp::Ok(v) => return state_from(&v),
                Resp::Err(_, b) if b["error"] == "not_leader" => {
                    target = b["leader"].as_str().and_then(node_index).unwrap_or((target + 1) % NODES.len());
                }
                _ => target = (target + 1) % NODES.len(),
            }
            if attempts > 1 {
                std::thread::sleep(Duration::from_millis(200));
            }
        }
        None
    }

    /// Where the membership changes: once faults have stopped, every node is
    /// made a voter again, so that what follows can ask the same of every
    /// node as in a run whose membership is fixed. A leader in a joint
    /// configuration is asked to leave it; one that lacks voters is asked to
    /// add them.
    fn reunite(&self, deadline: Instant) -> bool {
        let mut last = String::new();
        while Instant::now() < deadline {
            let statuses: Vec<Option<Value>> = (0..NODES.len())
                .map(|i| match self.client.call(i, "GET", "/status") {
                    Resp::Ok(v) => Some(v),
                    _ => None,
                })
                .collect();
            if let Some(i) = latest_leader(&statuses) {
                let v = statuses[i].as_ref().unwrap();
                let (voters, outgoing) = (names_of(&v["voters"]), names_of(&v["outgoing"]));
                let missing: Vec<&str> = NODES.iter().map(String::as_str).filter(|n| !voters.iter().any(|v| v == n)).collect();
                let wait = format!("{} leads term {} with voters {:?}, before them {:?}", NODES[i], v["term"], voters, outgoing);
                if wait != last {
                    log(&format!("eventually: waiting for every node to be a voter: {wait}"));
                    last = wait;
                }
                if !outgoing.is_empty() {
                    let _ = self.client.call(i, "POST", "/conf?leave=1");
                } else if missing.is_empty() {
                    return true;
                } else {
                    let _ = self.client.call(i, "POST", &format!("/conf?add={}", missing.join(",")));
                }
            }
            std::thread::sleep(Duration::from_millis(500));
        }
        false
    }

    fn eventually(&self) {
        let Ok(_once) = self.eventually_lock.try_lock() else { return };
        let _quiet = self.quiesce.write().unwrap_or_else(|e| e.into_inner());
        log("eventually: stopping faults");
        if let Ok(cmd) = std::env::var("ANTITHESIS_STOP_FAULTS") {
            match std::process::Command::new(&cmd).arg("3600").status() {
                Ok(s) => log(&format!("eventually: {cmd} exited {s}")),
                Err(e) => log(&format!("eventually: cannot run {cmd}: {e}")),
            }
        }

        // 1. Recovery: every node answers, they agree on a leader, and a
        //    write through it commits. (Where the membership changes, every
        //    node is first made a voter again.)
        let deadline = Instant::now() + Duration::from_secs(180);
        if self.conf_bucket.rate > 0.0 {
            let reunited = self.reunite(deadline);
            log(&format!("eventually: every node is a voter again: {reunited}"));
            if reunited {
                steps::sometimes(REUNITED, true, &json!({}));
            }
        }
        let mut recovered = None;
        let mut last_wait = String::new();
        while Instant::now() < deadline {
            let statuses: Vec<Option<Value>> = (0..NODES.len())
                .map(|i| match self.client.call(i, "GET", "/status") {
                    Resp::Ok(v) => Some(v),
                    _ => None,
                })
                .collect();
            let wait = describe_statuses(&statuses);
            if wait != last_wait {
                log(&format!("eventually: waiting for recovery: {wait}"));
                last_wait = wait;
            }
            if let Some(leader) = agreed_leader(&statuses) {
                let value = 1;
                if let (Outcome::Acked { index, .. }, _) = self.add_once(leader, value) {
                    recovered = Some((leader, index));
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(250));
        }
        log("eventually: assertions start");
        assert_always!(
            recovered.is_some(),
            "the cluster recovers once faults stop",
            &json!({"waiting_for": last_wait})
        );
        let Some((leader, write_index)) = recovered else {
            self.check_trace();
            log("eventually: ending timeline (cluster did not recover)");
            std::process::exit(0);
        };

        // 2. Convergence: every node applies up to that write, and they hold
        //    the same state there.
        let deadline = Instant::now() + Duration::from_secs(60);
        let mut states: Vec<Option<StateAt>> = vec![None; NODES.len()];
        while Instant::now() < deadline {
            for i in 0..NODES.len() {
                if let Resp::Ok(v) = self.client.call(i, "GET", "/sum?mode=stale") {
                    states[i] = state_from(&v);
                }
            }
            // A write sent before the faults stopped can still be applied
            // after this one (more so where followers pass writes on): wait
            // until the nodes are at the same place, not only past it.
            let past = states.iter().all(|s| s.as_ref().is_some_and(|s| s.index >= write_index));
            let level = states.iter().flatten().all(|s| Some(s.index) == states[0].as_ref().map(|s0| s0.index));
            if past && level {
                break;
            }
            std::thread::sleep(Duration::from_millis(250));
        }
        let converged = states.iter().all(|s| s.as_ref().is_some_and(|s| s.index >= write_index));
        let summary: Vec<Value> = states
            .iter()
            .map(|s| match s {
                Some(s) => json!({"node": s.node, "index": s.index, "sum": s.sum, "count": s.count, "digest": s.digest.to_string()}),
                None => Value::Null,
            })
            .collect();
        let same = converged && {
            let s0 = states[0].as_ref().unwrap();
            states.iter().flatten().all(|s| (s.index, s.sum, s.count, s.digest) == (s0.index, s0.sum, s0.count, s0.digest))
        };
        assert_always!(
            converged && same,
            "every node converges to the same state once faults stop",
            &json!({"write_index": write_index, "states": summary})
        );

        // 3. Durability: a linearizable read covers every acknowledged
        //    write, and matches the history the nodes applied.
        // Leadership can still move after recovery (a node that ran for
        // election during a partition has a higher term), so follow it.
        let read = self.linear_read_until(leader, Instant::now() + Duration::from_secs(60));
        std::thread::sleep(Duration::from_secs(1)); // Let the last log lines arrive.
        let max_acked = self.model().max_acked_index;
        assert_always!(
            read.as_ref().is_some_and(|r| r.index >= max_acked),
            "acknowledged writes survive once faults stop",
            &json!({"read": read.as_ref().map(|r| json!({"index": r.index, "sum": r.sum})), "max_acked_index": max_acked})
        );
        {
            let m = self.model();
            let mut missing = Vec::new();
            for (op, index) in m.acked_ops() {
                if let Some(a) = m.applied_at(index) {
                    if a.op != op {
                        missing.push(json!({"op": op, "index": index, "applied_op": a.op}));
                    }
                }
            }
            assert_always!(
                missing.is_empty(),
                "every acknowledged write is in the final history",
                &json!({"missing": missing})
            );
        }
        if let Some(r) = read {
            self.model().observe_state(r, StateSource::LinearRead);
        }
        self.check_trace();
        log("eventually: ending timeline");
        std::process::exit(0);
    }

    /// At the end of a timeline the stream check should have matched
    /// everything the nodes did up to now.
    fn check_trace(&self) {
        let deadline = Instant::now() + Duration::from_secs(60);
        if self.trace.checking {
            let written = self.trace.events.load(Ordering::Relaxed);
            while self.trace.matched() < written && !self.trace.stopped() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(100));
            }
            let matched = self.trace.matched();
            report_notes(&self.trace);
            log(&format!("eventually: stream check matched {matched} events, {written} written before it was asked"));
            if !self.trace.stopped() {
                assert_always!(
                    matched >= written,
                    "the stream check keeps up with the run",
                    &json!({"written": written, "matched": matched})
                );
                if matched >= written {
                    assert_reachable!(
                        "a timeline's whole stream is matched by the model",
                        &json!({"events": matched})
                    );
                }
            }
        }
    }
}

/// Steps the trace spec names with TraceKit's Note. spec/EtcdBinding.tla
/// makes none, so any note is unexpected.
fn report_notes(trace: &trace::Trace) {
    for (k, name) in trace.new_notes() {
        antithesis_sdk::assert_unreachable!(
            "the trace spec makes no note the driver does not know",
            &json!({"event_index": k, "note": name})
        );
    }
}

fn describe_statuses(statuses: &[Option<Value>]) -> String {
    statuses
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            Some(v) => format!("{}={}/t{}/leader={}", NODES[i], v["state"], v["term"], v["leader"]),
            None => format!("{}=down", NODES[i]),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn names_of(v: &Value) -> Vec<String> {
    v.as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
}

/// The node that says it leads, in the latest term if several do.
fn latest_leader(statuses: &[Option<Value>]) -> Option<usize> {
    statuses
        .iter()
        .enumerate()
        .filter_map(|(i, s)| s.as_ref().filter(|v| v["state"] == "leader").map(|v| (v["term"].as_u64().unwrap_or(0), i)))
        .max()
        .map(|(_, i)| i)
}

/// The node that leads, if every node answers and every node of the leader's
/// configuration (its voters, the voters before a joint change, its
/// learners) agrees that it does, in the same term. A leader tells nothing
/// to a node outside its configuration, so those are not asked. Where the
/// membership is fixed that is every node.
fn agreed_leader(statuses: &[Option<Value>]) -> Option<usize> {
    if statuses.iter().flatten().count() != NODES.len() {
        return None;
    }
    let i = latest_leader(statuses)?;
    let v = statuses[i].as_ref()?;
    let term = v["term"].as_u64()?;
    let mut members = names_of(&v["voters"]);
    members.extend(names_of(&v["outgoing"]));
    members.extend(names_of(&v["learners"]));
    let ok = members.iter().all(|m| {
        node_index(m)
            .and_then(|j| statuses[j].as_ref())
            .is_some_and(|w| w["leader"].as_str() == Some(NODES[i].as_str()) && w["term"].as_u64() == Some(term))
    });
    (ok && members.iter().any(|m| *m == NODES[i])).then_some(i)
}

impl Driver {
    fn add(&self, tc: TestCase) {
        let target = self.pick_target(&tc);
        let value = tc.draw(gs::integers::<i64>().min_value(-1000).max_value(1000));
        let retry = tc.draw(gs::weighted_booleans(0.9));
        if !self.add_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let (outcome, hint) = self.add_once(target, value);
        // A real client follows the redirect once, as a new request.
        if let (Outcome::Rejected, Some(leader), true) = (outcome, hint, retry) {
            if leader != target {
                if let (Outcome::Acked { .. }, _) = self.add_once(leader, value) {
                    assert_reachable!("a write redirected to the leader succeeds", &json!({}));
                }
            }
        }
    }

    fn linear_read(&self, tc: TestCase) {
        let target = self.pick_target(&tc);
        if !self.linear_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let (acked_floor, read_floor) = {
            let m = self.model();
            (m.max_acked_index, m.max_linear_read_index)
        };
        match self.client.call(target, "GET", "/sum") {
            Resp::Ok(v) => {
                let st = state_from(&v);
                assert_always!(st.is_some(), "a linearizable read returns a well-formed state", &json!({"body": v}));
                let Some(st) = st else { return };
                self.leader_hint.store(target, Ordering::Relaxed);
                assert_always!(
                    st.index >= acked_floor,
                    "a linearizable read reflects every write acknowledged before it started",
                    &json!({"node": st.node, "read_index": st.index, "max_acked_index_at_start": acked_floor})
                );
                assert_always!(
                    st.index >= read_floor,
                    "a linearizable read never returns an older state than a completed one",
                    &json!({"node": st.node, "read_index": st.index, "max_read_index_at_start": read_floor})
                );
                let mut m = self.model();
                m.max_linear_read_index = m.max_linear_read_index.max(st.index);
                m.observe_state(st, StateSource::LinearRead);
            }
            Resp::Err(_, b) if b["error"] == "not_leader" => self.update_hint(&b),
            Resp::Err(..) | Resp::NoAnswer(_) => {
                assert_reachable!("a linearizable read fails without an answer", &json!({"node": NODES[target]}));
            }
        }
    }

    fn stale_read(&self, tc: TestCase) {
        let random = tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1));
        // Half the time, read from the node furthest behind, by its logs.
        let target = if tc.draw(gs::booleans()) { self.most_lagging().unwrap_or(random) } else { random };
        if !self.stale_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let acked_floor = self.model().max_acked_index;
        if let Resp::Ok(v) = self.client.call(target, "GET", "/sum?mode=stale") {
            if let Some(st) = state_from(&v) {
                assert_sometimes_greater_than!(
                    acked_floor as i64 - st.index as i64,
                    50i64,
                    "a stale read trails acknowledged writes by more than 50 entries",
                    &json!({"node": st.node, "read_index": st.index, "max_acked_index_at_start": acked_floor})
                );
                self.model().observe_state(st, StateSource::StaleRead);
            }
        }
    }

    /// Asks a node, usually the leader, to hand leadership to another.
    fn transfer(&self, tc: TestCase) {
        if self.transfer_bucket.rate <= 0.0 {
            return;
        }
        let from = self.pick_target(&tc);
        let to = tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1));
        if !self.transfer_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        if let Resp::Ok(v) = self.client.call(from, "POST", &format!("/transfer?to={}", NODES[to])) {
            if v["state"] == "leader" && from != to {
                steps::sometimes(TRANSFER_ASKED, true, &json!({"from": NODES[from], "to": NODES[to]}));
            }
        }
    }

    /// Asks a node, usually the leader, for a change of membership: usually
    /// of one node, sometimes of several at once (a joint change), sometimes
    /// to leave a joint configuration. What is asked depends on the
    /// configuration the node has, so that most changes change something.
    /// The first node is never removed (the server refuses it too), so no
    /// change removes every voter.
    fn conf(&self, tc: TestCase) {
        if self.conf_bucket.rate <= 0.0 {
            return;
        }
        let target = self.pick_target(&tc);
        let kind = tc.draw(gs::integers::<usize>().max_value(9));
        let picks: Vec<(usize, usize)> = (0..3)
            .map(|_| (tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1)), tc.draw(gs::integers::<usize>().max_value(9))))
            .collect();
        if !self.conf_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let Resp::Ok(status) = self.client.call(target, "GET", "/status") else { return };
        let (voters, outgoing) = (names_of(&status["voters"]), names_of(&status["outgoing"]));
        let leave = kind == 0 || (!outgoing.is_empty() && kind < 6);
        let joint = !leave && kind >= 7;
        let path = if leave {
            "/conf?leave=1".to_string()
        } else {
            let (mut add, mut remove, mut learner) = (Vec::new(), Vec::new(), Vec::new());
            let mut used = Vec::new();
            for &(i, what) in picks.iter().take(if joint { 1 + kind % 3 } else { 1 }) {
                if used.contains(&i) {
                    continue;
                }
                used.push(i);
                let is_voter = voters.iter().any(|v| *v == NODES[i]);
                match (i, is_voter, what) {
                    (0, _, _) => add.push(NODES[i].as_str()),
                    (_, true, 0..=6) => remove.push(NODES[i].as_str()),
                    (_, true, 7) | (_, false, 0..=1) => learner.push(NODES[i].as_str()),
                    (_, false, 2) => remove.push(NODES[i].as_str()),
                    _ => add.push(NODES[i].as_str()),
                }
            }
            let mut q = Vec::new();
            for (key, names) in [("add", &add), ("remove", &remove), ("learner", &learner)] {
                if !names.is_empty() {
                    q.push(format!("{key}={}", names.join(",")));
                }
            }
            if joint {
                q.push(format!("mode={}", ["auto", "implicit", "explicit"][kind - 7]));
            } else if kind <= 2 {
                q.push("v1=1".to_string());
            }
            format!("/conf?{}", q.join("&"))
        };
        if let Resp::Ok(v) = self.client.call(target, "POST", &path) {
            if v["state"] == "leader" {
                steps::sometimes(CONF_ASKED, true, &json!({"node": NODES[target], "path": path}));
                if joint {
                    steps::sometimes(CONF_JOINT_ASKED, true, &json!({"node": NODES[target], "path": path}));
                }
                if leave && !outgoing.is_empty() {
                    steps::sometimes(CONF_LEAVE_ASKED, true, &json!({"node": NODES[target]}));
                }
            }
        }
    }

    fn eventually_rule(&self, tc: TestCase) {
        if !self.eventually_enabled {
            return;
        }
        let full = self.trace.checking && self.trace.events.load(Ordering::Relaxed) >= TRACE_LIMIT;
        if tc.draw(gs::weighted_booleans(EVENTUALLY_P)) || full {
            self.eventually();
        }
    }
}

/// Waits until every node answers and a linearizable read succeeds.
fn wait_for_cluster(client: &Client) {
    let mut last = String::new();
    loop {
        let statuses: Vec<Option<Value>> = (0..NODES.len())
            .map(|i| match client.call(i, "GET", "/status") {
                Resp::Ok(v) => Some(v),
                _ => None,
            })
            .collect();
        let mut msg = describe_statuses(&statuses);
        if let Some(leader) = agreed_leader(&statuses) {
            match client.call(leader, "GET", "/sum") {
                Resp::Ok(_) => {
                    log(&format!("cluster ready: {msg}"));
                    return;
                }
                Resp::Err(c, b) => msg.push_str(&format!(" read={c} {b}")),
                Resp::NoAnswer(e) => msg.push_str(&format!(" read={e}")),
            }
        }
        if msg != last {
            log(&format!("waiting for cluster: {msg}"));
            last = msg;
        }
        std::thread::sleep(Duration::from_millis(200));
    }
}

#[hegel::main(phases = [hegel::Phase::Generate])]
fn main(tc: TestCase) {
    antithesis_sdk::antithesis_init();
    log(&format!(
        "net.unix.max_dgram_qlen={}",
        std::fs::read_to_string("/proc/sys/net/unix/max_dgram_qlen").unwrap_or_default().trim()
    ));
    let mut steps = steps::Steps::default();
    let trace = trace::start(move |ev| steps.observe(ev));
    {
        let trace = trace.clone();
        std::thread::spawn(move || loop {
            report_notes(&trace);
            std::thread::sleep(Duration::from_millis(200));
        });
    }
    let model = Arc::new(Mutex::new(Model::new()));
    let logs = Logs::start(model.clone());
    let client = Client::new();

    wait_for_cluster(&client);
    antithesis_sdk::lifecycle::setup_complete(&json!({"nodes": *NODES}));
    log("setup complete; waiting for /workload-active");
    while !std::path::Path::new("/workload-active").exists() {
        std::thread::sleep(Duration::from_millis(100));
    }
    logs.active.store(true, Ordering::Relaxed);
    assert_reachable!("the workload starts", &json!({}));
    log("workload active");

    let eventually_enabled = std::env::var("DRIVER_EVENTUALLY").map_or(true, |v| v != "off");
    let driver = Arc::new(Driver {
        client,
        model,
        logs,
        leader_hint: AtomicUsize::new(0),
        quiesce: RwLock::new(()),
        eventually_lock: Mutex::new(()),
        eventually_enabled,
        trace,
        add_bucket: Bucket::new("DRIVER_ADD_RATE", DEFAULT_ADD_RATE),
        linear_bucket: Bucket::new("DRIVER_LINEAR_RATE", DEFAULT_LINEAR_RATE),
        stale_bucket: Bucket::new("DRIVER_STALE_RATE", DEFAULT_STALE_RATE),
        transfer_bucket: Bucket::new("DRIVER_TRANSFER_RATE", DEFAULT_TRANSFER_RATE),
        conf_bucket: Bucket::new("DRIVER_CONF_RATE", DEFAULT_CONF_RATE),
    });
    // What only some runs can reach is declared for those runs.
    if driver.transfer_bucket.rate > 0.0 {
        steps::sometimes(TRANSFER_ASKED, false, &json!({}));
    }
    if driver.conf_bucket.rate > 0.0 {
        for m in [CONF_ASKED, CONF_JOINT_ASKED, CONF_LEAVE_ASKED, REUNITED] {
            steps::sometimes(m, false, &json!({}));
        }
    }
    if std::env::var("FORWARD").is_ok_and(|v| v == "1") {
        steps::sometimes(FORWARDED, false, &json!({}));
    }
    // For the local loop: run the eventually after a fixed time.
    if let Some(secs) = std::env::var("DRIVER_EVENTUALLY_AFTER").ok().and_then(|v| v.parse::<u64>().ok()) {
        let d = driver.clone();
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(secs));
            d.eventually();
        });
    }
    machine(ArcDriver(driver)).max_concurrency(4).steps(i64::MAX).run_concurrent(tc);
}

/// The machine owns its model; this wrapper lets the eventually thread share it.
struct ArcDriver(Arc<Driver>);

#[hegel::concurrent_state_machine]
impl ArcDriver {
    #[rule(weight = 10.0)]
    fn add(&self, tc: TestCase) {
        self.0.add(tc)
    }

    #[rule(weight = 4.0)]
    fn linear_read(&self, tc: TestCase) {
        self.0.linear_read(tc)
    }

    #[rule(weight = 3.0)]
    fn stale_read(&self, tc: TestCase) {
        self.0.stale_read(tc)
    }

    #[rule(weight = 1.0)]
    fn transfer(&self, tc: TestCase) {
        self.0.transfer(tc)
    }

    #[rule(weight = 1.0)]
    fn conf(&self, tc: TestCase) {
        self.0.conf(tc)
    }

    #[rule(weight = 1.0)]
    fn eventually_rule(&self, tc: TestCase) {
        self.0.eventually_rule(tc)
    }
}
