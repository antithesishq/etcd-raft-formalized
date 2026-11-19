//! Properties of a single node, checked on the steps it reports (the
//! tracekit stream; see rawnode/node.go for the events). They hold whether or
//! not the stream check is running, and need nothing from the model.
//!
//! Also notes which paths that only faults reach a run got to. Raft's own
//! source has no assertions; these are made from what raft does at its
//! boundary.

use antithesis_sdk::assert::{assert_raw, AssertType};
use antithesis_sdk::{assert_always, assert_always_or_unreachable, assert_reachable};
use serde_json::{json, Value};
use std::collections::HashMap;

#[derive(Default)]
struct Node {
    booted: bool,
    term: u64,
    vote: String,
    commit: u64,
    /// Index of the last entry on disk, as announced.
    last: u64,
    role: String,
    /// Index of the last entry handed to the state machine since the boot.
    applied: u64,
    /// A write was announced and nothing has been reported since.
    wrote: bool,
    /// What is on disk, as the last write was announced. `term`, `vote`,
    /// `commit` and `last` are what raft has in memory; the two differ only
    /// where writes are made later (`mem`, `write`).
    dterm: u64,
    dvote: String,
    dcommit: u64,
    dlast: u64,
    /// Writes reported (`mem` with w = 1) and not announced yet.
    queued: u64,
    /// A write made later (`write`) is announced and not yet said to be made.
    inflight: bool,
    /// The message being handled.
    msg: Value,
    /// With PreVote: the pre-votes asked for since the node last changed
    /// role, as (peer, term).
    prevotes: Vec<(String, u64)>,
    /// The node takes one Ready for several inputs (`flush`): what a
    /// follower has in memory beyond its disk is then not reported.
    batch: bool,
    /// The term of the election the node started because its leader told
    /// it to (0: none).
    told: u64,
    /// The voters raft counts with, and the voters before a joint change
    /// that is not left yet; and whether a change has made them.
    voters: Vec<String>,
    outgoing: Vec<String>,
    changed: bool,
}

#[derive(Default)]
pub struct Steps {
    nodes: HashMap<String, Node>,
    declared_early: bool,
    declared_async: bool,
    declared_snaps: bool,
    declared_atonce: bool,
    declared_transfer: bool,
    declared_forward: bool,
    declared_batch: bool,
    declared_member: bool,
    declared_member_snap: bool,
}

/// Paths that only a run with writes made later can reach. They are
/// declared when the stream shows such a run, so that a run of the other
/// kind is not told it missed them.
const EARLY: &[&str] = &["a leader sends entries that are not on its disk yet"];
const ASYNC: &[&str] = &[
    "a node hands its state machine an entry before its commit index is on disk",
    "a node is handed a message while a write of its own waits",
    "a node is killed with a write waiting",
];

/// The two ways a kill can fall around a write. They are expected of a run
/// whose nodes announce a write and make it at once (`ready`). Where writes
/// are made later, the time between a write and the report that it is made
/// is too short for a run to be told it missed one of them.
const ATONCE: &[&str] = &[
    "a node is killed just after a write and has it when it restarts",
    "a node is killed during a write and does not have it when it restarts",
];

/// Paths that only a run in which nodes take snapshots can reach.
const SNAPS: &[&str] = &[
    "a follower's log is replaced by a snapshot its leader sent",
    "a node starts again from a snapshot",
];

/// Paths that only a run in which leadership is handed over can reach.
const TRANSFER: &[&str] = &[
    "a node starts an election because its leader told it to",
    "a node that its leader told to start an election wins it",
];

/// Only a run in which followers pass proposals on.
const FORWARD: &[&str] = &["a leader appends an entry that a follower passed on to it"];

/// Only a run in which a node takes one Ready for several inputs.
const BATCH: &[&str] = &[
    "a node makes one write for several inputs",
    "a node is killed with input it has not taken a Ready for",
];

/// Only a run in which the membership changes.
const MEMBER: &[&str] = &[
    "a node counts with a joint configuration",
    "a node leaves a joint configuration",
    "a leader applies a change that removes it from the voters",
    "a node is elected with voters that a change of membership made",
];

/// Only a run in which the membership changes and nodes take snapshots.
const MEMBER_SNAP: &str = "a node starts again with the voters its snapshot holds";

fn names(v: &Value) -> Vec<String> {
    v.as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
}

pub fn sometimes(message: &str, hit: bool, details: &Value) {
    assert_raw(
        hit, message.to_string(), details, String::new(), String::new(), String::new(), 0, 0, hit, true,
        AssertType::Reachability, "Reachable".to_string(), message.to_string(),
    );
}

impl Steps {
    pub fn observe(&mut self, ev: &Value) {
        let Some(name) = ev["node"].as_str() else { return };
        if !self.declared_transfer && ev["msg"]["type"] == "timeoutnow" {
            self.declared_transfer = true;
            TRANSFER.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        if !self.declared_forward && ev["msg"]["type"] == "prop" {
            self.declared_forward = true;
            FORWARD.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        if !self.declared_batch && ev["e"] == "flush" {
            self.declared_batch = true;
            BATCH.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        // A leader can send before it writes where a write is announced
        // apart from what raft did in memory and the node does not batch
        // (`write`), or with AsyncStorageWrites (`a`).
        if !self.declared_early && (ev["e"] == "write" || !ev["a"].is_null()) {
            self.declared_early = true;
            EARLY.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        if !self.declared_async && (!ev["cause"].is_null() || !ev["a"].is_null()) {
            self.declared_async = true;
            ASYNC.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        // (A batching node reports `ready` only at its start and for a
        // snapshot from a leader.)
        if !self.declared_atonce && ev["e"] == "ready" && ev["by"] != "boot" && !self.declared_batch {
            self.declared_atonce = true;
            ATONCE.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        if !self.declared_member && ev["e"] == "conf" {
            self.declared_member = true;
            MEMBER.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        if !self.declared_member_snap && (self.declared_member || ev["e"] == "conf") && (self.declared_snaps || ev["e"] == "snap") {
            self.declared_member_snap = true;
            sometimes(MEMBER_SNAP, false, &json!({}));
        }
        if !self.declared_snaps && ev["e"] == "snap" {
            self.declared_snaps = true;
            SNAPS.iter().for_each(|m| sometimes(m, false, &json!({})));
        }
        let n = self.nodes.entry(name.to_string()).or_default();
        let num = |v: &Value| v.as_u64().unwrap_or(0);
        match ev["e"].as_str().unwrap_or("") {
            // What the node recovered from disk. A write announced just before
            // a kill may not have been made, so this replaces what was announced.
            "boot" => {
                let (term, vote, commit, last) =
                    (num(&ev["term"]), ev["vote"].as_str().unwrap_or("").to_string(), num(&ev["commit"]), num(&ev["lastIndex"]));
                assert_always!(
                    commit <= last,
                    "a restarted node's commit index is within its log",
                    &json!({"node": name, "commit_index": commit, "last_index": last, "k": ev["k"]})
                );
                if num(&ev["applied"]) > 0 {
                    sometimes(SNAPS[1], true, &json!({"node": name}));
                }
                if n.booted && n.queued > 0 {
                    if n.batch {
                        sometimes(BATCH[1], true, &json!({"node": name}));
                    }
                    if !n.batch || self.declared_async {
                        sometimes(ASYNC[2], true, &json!({"node": name}));
                    }
                }
                if n.booted && n.wrote {
                    if (term, &vote, commit, last) == (n.dterm, &n.dvote, n.dcommit, n.dlast) {
                        sometimes(ATONCE[0], true, &json!({"node": name}));
                    } else {
                        sometimes(ATONCE[1], true, &json!({"node": name}));
                    }
                }
                *n = Node {
                    booted: true, term, vote: vote.clone(), commit, last, role: "follower".into(),
                    dterm: term, dvote: vote, dcommit: commit, dlast: last, applied: num(&ev["applied"]),
                    voters: names(&ev["voters"]), outgoing: names(&ev["outgoing"]),
                    ..Default::default()
                };
                // A snapshot taken after a change holds what the change made.
                if num(&ev["applied"]) > 0 && self.declared_member {
                    n.changed = true;
                    sometimes(MEMBER_SNAP, true, &json!({"node": name, "voters": ev["voters"]}));
                }
            }
            // Raft is told that a change of membership is applied.
            "conf" => {
                let (voters, outgoing) = (names(&ev["voters"]), names(&ev["outgoing"]));
                if !outgoing.is_empty() {
                    sometimes(MEMBER[0], true, &json!({"node": name, "voters": voters, "before": outgoing}));
                }
                if outgoing.is_empty() && !n.outgoing.is_empty() {
                    sometimes(MEMBER[1], true, &json!({"node": name, "voters": voters}));
                }
                if n.role == "leader" && !voters.iter().any(|v| v == name) && n.voters.iter().any(|v| v == name) {
                    sometimes(MEMBER[2], true, &json!({"node": name, "voters": voters}));
                }
                n.voters = voters;
                n.outgoing = outgoing;
                n.changed = true;
            }
            "recv" => {
                if n.queued > 0 || n.inflight {
                    sometimes(ASYNC[1], true, &json!({"node": name}));
                }
                n.msg = ev["msg"].clone()
            }
            // The write of the oldest `mem` not yet written, announced: the
            // same properties, of what is on disk.
            // A batching node: the oldest `mem` is part of the write that
            // `net` announces.
            "flush" => {
                n.batch = true;
                n.queued = n.queued.saturating_sub(1);
                if ev["more"] == 1 {
                    sometimes(BATCH[0], true, &json!({"node": name}));
                }
            }
            "write" | "net" => {
                let (term, vote, commit) = (num(&ev["term"]), ev["vote"].as_str().unwrap_or("").to_string(), num(&ev["commit"]));
                let first = num(&ev["first"]);
                let count = ev["entries"].as_array().map_or(0, |a| a.len() as u64);
                assert_always_or_unreachable!(
                    term >= n.dterm,
                    "the term on a node's disk never decreases",
                    &json!({"node": name, "old_term": n.dterm, "new_term": term, "k": ev["k"]})
                );
                assert_always_or_unreachable!(
                    term != n.dterm || n.dvote.is_empty() || n.dvote == vote,
                    "the vote on a node's disk is for at most one candidate per term",
                    &json!({"node": name, "term": term, "candidate": vote, "prev_candidate": n.dvote, "k": ev["k"]})
                );
                assert_always_or_unreachable!(
                    commit >= n.dcommit,
                    "the commit index on a node's disk never decreases",
                    &json!({"node": name, "old_commit": n.dcommit, "new_commit": commit, "k": ev["k"]})
                );
                if count > 0 {
                    assert_always_or_unreachable!(
                        first > n.dcommit && first <= n.dlast + 1,
                        "a write neither overwrites committed entries nor leaves a hole in the log",
                        &json!({"node": name, "first": first, "commit_index": n.dcommit, "last_index": n.dlast, "k": ev["k"]})
                    );
                    // A batching node says where entries go only here.
                    if ev["e"] == "net" {
                        assert_always!(
                            first > n.dcommit,
                            "a node never overwrites committed log entries",
                            &json!({"node": name, "first": first, "commit_index": n.dcommit, "k": ev["k"]})
                        );
                        assert_always!(
                            first <= n.dlast + 1,
                            "a node's log has no holes",
                            &json!({"node": name, "first": first, "last_index": n.dlast, "k": ev["k"]})
                        );
                        if first <= n.dlast && n.role != "leader" {
                            assert_reachable!("a follower deletes the end of its log", &json!({"node": name}));
                        }
                    }
                    n.dlast = first + count - 1;
                }
                // The log is replaced by a snapshot a leader sent.
                if !ev["snap"].is_null() {
                    n.dlast = num(&ev["snap"]["index"]);
                }
                assert_always_or_unreachable!(
                    commit <= n.dlast,
                    "the commit index on a node's disk is within the log on its disk",
                    &json!({"node": name, "commit_index": commit, "last_index": n.dlast, "k": ev["k"]})
                );
                n.dterm = term;
                n.dvote = vote;
                n.dcommit = commit;
                if ev["e"] == "write" {
                    n.queued = n.queued.saturating_sub(1);
                }
                n.wrote = true;
                n.inflight = true;
            }
            "wrote" => {
                n.wrote = false;
                n.inflight = false;
            }
            // The state machine is replaced by a snapshot a leader sent.
            "restore" => {
                if ev["a"].is_null() {
                    n.wrote = false;
                }
                n.applied = num(&ev["index"]);
                if !ev["voters"].is_null() {
                    n.voters = names(&ev["voters"]);
                    n.outgoing = names(&ev["outgoing"]);
                }
            }
            "ready" | "mem" => {
                let later = ev["e"] == "mem";
                let (term, vote, commit) = (num(&ev["term"]), ev["vote"].as_str().unwrap_or("").to_string(), num(&ev["commit"]));
                let role = ev["role"].as_str().unwrap_or("").to_string();
                let first = num(&ev["first"]);
                let count = ev["entries"].as_array().map_or(0, |a| a.len() as u64);
                assert_always!(
                    term >= n.term,
                    "a node's current term never decreases",
                    &json!({"node": name, "old_term": n.term, "new_term": term, "k": ev["k"]})
                );
                assert_always!(
                    term != n.term || n.vote.is_empty() || n.vote == vote,
                    "a node votes for at most one candidate per term",
                    &json!({"node": name, "term": term, "candidate": vote, "prev_candidate": n.vote, "k": ev["k"]})
                );
                assert_always!(
                    commit >= n.commit,
                    "a node's commit index never decreases",
                    &json!({"node": name, "old_commit": n.commit, "new_commit": commit, "k": ev["k"]})
                );
                // A batching node does not say where the entries go.
                let placed = !ev["first"].is_null();
                if later && !placed {
                    n.batch = true;
                    n.last += count;
                }
                if count > 0 && placed {
                    assert_always!(
                        first > n.commit,
                        "a node never overwrites committed log entries",
                        &json!({"node": name, "first": first, "commit_index": n.commit, "k": ev["k"]})
                    );
                    assert_always!(
                        first <= n.last + 1,
                        "a node's log has no holes",
                        &json!({"node": name, "first": first, "last_index": n.last, "k": ev["k"]})
                    );
                    if first <= n.last {
                        assert_reachable!("a follower deletes the end of its log", &json!({"node": name}));
                    }
                    n.last = first + count - 1;
                }
                if !ev["snap"].is_null() {
                    n.last = num(&ev["snap"]["index"]);
                    sometimes(SNAPS[0], true, &json!({"node": name}));
                }
                // (What a batching follower has in memory is not reported.)
                assert_always!(
                    n.batch || commit <= n.last,
                    "a node's commit index is within its log",
                    &json!({"node": name, "commit_index": commit, "last_index": n.last, "k": ev["k"]})
                );
                if ev["by"] == "recv" && n.msg["type"] == "timeoutnow" && role == "candidate" && term > n.term {
                    n.told = term;
                    sometimes(TRANSFER[0], true, &json!({"node": name}));
                }
                if role == "leader" && n.role != "leader" && n.told == term {
                    sometimes(TRANSFER[1], true, &json!({"node": name}));
                }
                if role == "leader" && n.role != "leader" && n.changed {
                    sometimes(MEMBER[3], true, &json!({"node": name, "voters": n.voters, "before": n.outgoing}));
                }
                if ev["by"] == "recv" && n.msg["type"] == "prop" && role == "leader" && count > 0 {
                    sometimes(FORWARD[0], true, &json!({"node": name}));
                }
                if term > n.term && n.role == "leader" {
                    assert_reachable!("a leader learns of a later term and steps down", &json!({"node": name}));
                }
                if term > n.term && role == "candidate" && n.role == "candidate" {
                    assert_reachable!("a candidate's election ends without a winner and it starts another", &json!({"node": name}));
                }
                if commit > n.commit && role != "leader" && n.msg["type"] == "hb" && ev["by"] == "recv" {
                    assert_reachable!("a follower moves its commit index on a heartbeat", &json!({"node": name}));
                }
                if role != n.role {
                    n.prevotes.clear();
                }
                if later {
                    n.queued += num(&ev["w"]);
                } else {
                    n.wrote = (term, &vote, commit) != (n.term, &n.vote, n.commit) || count > 0;
                    if n.batch {
                        // What it has in memory was not all reported: this
                        // write says what its log is from here on.
                        if count > 0 {
                            n.last = first + count - 1;
                        } else if ev["snap"].is_null() {
                            n.last = n.dlast;
                        }
                    }
                    (n.dterm, n.dvote, n.dcommit, n.dlast) = (term, vote.clone(), commit, n.last);
                }
                n.term = term;
                n.vote = vote;
                n.commit = commit;
                n.role = role;
            }
            "send" => {
                // Where writes are made later, `wrote` says when one is made.
                if ev["cause"].is_null() && ev["b"].is_null() && n.queued == 0 {
                    n.wrote = false;
                }
                let m = &ev["msg"];
                if m["type"] == "app" && num(&m["index"]) + m["entries"].as_array().map_or(0, |a| a.len() as u64) > n.dlast {
                    sometimes(EARLY[0], true, &json!({"node": name}));
                }
                let reject = m["reject"].as_bool().unwrap_or(false);
                match m["type"].as_str().unwrap_or("") {
                    // With PreVote a node that finds no quorum asks again
                    // without changing its term or role.
                    "prevote" => {
                        let key = (m["to"].as_str().unwrap_or("").to_string(), num(&m["term"]));
                        if n.prevotes.contains(&key) {
                            assert_reachable!("a candidate's election ends without a winner and it starts another", &json!({"node": name}));
                        } else {
                            n.prevotes.push(key);
                        }
                    }
                    "voteresp" if reject => assert_reachable!("a node refuses its vote", &json!({"node": name})),
                    "appresp" if reject => assert_reachable!("a follower refuses a request to append", &json!({"node": name})),
                    _ => {}
                }
            }
            // Entries handed to the state machine. Whether they are the
            // entries of the node's log is the stream check's to say.
            "apply" => {
                if ev["a"].is_null() {
                    n.wrote = false;
                }
                let first = num(&ev["first"]);
                let count = ev["entries"].as_array().map_or(0, |a| a.len() as u64);
                assert_always!(
                    first == n.applied + 1,
                    "a node hands entries to its state machine in index order, none skipped",
                    &json!({"node": name, "first": first, "prev_index": n.applied, "k": ev["k"]})
                );
                assert_always!(
                    first + count - 1 <= n.commit,
                    "a node hands its state machine only entries within its commit index",
                    &json!({"node": name, "last": first + count - 1, "commit_index": n.commit, "k": ev["k"]})
                );
                n.applied = first + count - 1;
                if n.applied > n.dcommit {
                    sometimes(ASYNC[0], true, &json!({"node": name}));
                }
            }
            _ => {}
        }
    }
}
