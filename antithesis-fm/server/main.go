// A tiny replicated service built on etcd-io/raft (binary name raft-sum):
// three nodes keep a running sum of integers sent by clients. It exists to
// be tested in Antithesis. Raft runs as a RawNode on one goroutine, through
// package rawnode, which reports every step raft takes at its boundary.
//
// It logs one line per role change (msg=raft-state) and per applied add
// (msg=raft-apply). The harness forwards those lines to the driver.
package main

import (
	"context"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"log"
	"math/rand/v2"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/antithesishq/antithesis-sdk-go/assert"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"

	"etcd-raft-formalized/rawnode"
	"tracekit"
)

var stderrMu sync.Mutex

// logLine writes one structured line to stderr in a single write.
func logLine(format string, args ...any) {
	s := fmt.Sprintf(format, args...) + "\n"
	stderrMu.Lock()
	_, _ = os.Stderr.WriteString(s)
	stderrMu.Unlock()
}

type lockedWriter struct{}

func (lockedWriter) Write(p []byte) (int, error) {
	stderrMu.Lock()
	defer stderrMu.Unlock()
	return os.Stderr.Write(p)
}

func env(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

func envDuration(key string, def time.Duration) time.Duration {
	if v := os.Getenv(key); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			fatal("bad %s: %v", key, err)
		}
		return d
	}
	return def
}

func envUint(key string, def uint64) uint64 {
	if v := os.Getenv(key); v != "" {
		n, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			fatal("bad %s: %v", key, err)
		}
		return n
	}
	return def
}

func fatal(format string, args ...any) {
	logLine("fatal: "+format, args...)
	os.Exit(1)
}

// status is what the HTTP handlers may know of raft, published by raft's
// goroutine after every step.
type status struct {
	State     string
	Term      uint64
	Leader    string
	Commit    uint64
	Applied   uint64
	LastIndex uint64
	// The configuration raft counts with: the voters, the voters before a
	// joint change that is not left yet, and the learners.
	Voters, Outgoing, Learners []string
}

type waitKey struct {
	kind byte
	op   uint64
}

// proposal is a command a handler wants in the log.
type proposal struct {
	cmd      command
	proposed chan error    // nil: raft appended it
	applied  chan fsmState // the state machine after this node applied it
}

type server struct {
	id     string
	names  map[uint64]string
	fsm    *sumFSM
	status atomic.Pointer[status]
	props  chan *proposal

	mu      sync.Mutex
	waiters map[waitKey]*proposal

	// With READ_INDEX: linearizable reads ask raft for a read index instead of
	// putting an entry in the log.
	snapEvery uint64
	// With FORWARD a follower passes a proposal on to its leader, so a node
	// that knows a leader takes writes.
	forward   bool
	transfers chan uint64 // nodes leadership is to be handed to
	// Changes of membership to ask raft for, and the node that no change may
	// remove (KEEP): a change that removes every voter makes raft panic.
	confs     chan pb.ConfChangeI
	keep      uint64
	readIndex bool
	reads     chan *read
	applied   atomic.Uint64 // index of the last entry handed to the state machine
}

// read is a linearizable read waiting for raft's read index.
type read struct {
	id    uint64
	asked time.Time
	done  chan fsmState
}

func main() {
	id := env("NODE_ID", "")
	if id == "" {
		fatal("NODE_ID is required")
	}
	httpBind := env("HTTP_BIND", "0.0.0.0:8000")
	raftBind := env("RAFT_BIND", "0.0.0.0:7000")
	dataDir := env("DATA_DIR", "/data")

	// PEERS is "name=host:port,..."; a node's raft id is its place in it.
	var self uint64
	var ids []uint64
	names := map[uint64]string{}
	addrs := map[uint64]string{}
	for i, p := range strings.Split(env("PEERS", ""), ",") {
		kv := strings.SplitN(p, "=", 2)
		if len(kv) != 2 {
			fatal("bad PEERS entry %q", p)
		}
		n := uint64(i + 1)
		ids = append(ids, n)
		names[n], addrs[n] = kv[0], kv[1]
		if kv[0] == id {
			self = n
		}
	}
	if self == 0 {
		fatal("NODE_ID %q is not in PEERS", id)
	}
	// VOTERS: the names of the nodes that are voters at the start, the same
	// on every node. Without it every node of PEERS is one.
	voters := ids
	if v := env("VOTERS", ""); v != "" {
		voters = nil
		for _, name := range strings.Split(v, ",") {
			found := false
			for n, have := range names {
				if have == name {
					voters, found = append(voters, n), true
				}
			}
			if !found {
				fatal("VOTERS: %q is not in PEERS", name)
			}
		}
	}
	if err := os.MkdirAll(dataDir, 0o755); err != nil {
		fatal("mkdir: %v", err)
	}
	disk, err := rawnode.OpenBolt(filepath.Join(dataDir, "raft.db"))
	if err != nil {
		fatal("open disk: %v", err)
	}

	logger := &raft.DefaultLogger{Logger: log.New(lockedWriter{}, "raft ", 0)}
	level := env("RAFT_LOG_LEVEL", "info")
	if level == "debug" || level == "trace" {
		logger.EnableDebug()
	}
	// Every step raft takes at its boundary is reported through one sink:
	// to the log at trace level, and to a checker if one is listening.
	sink := tracekit.New(func(msg string, kv ...any) {
		if level == "trace" {
			b, _ := json.Marshal(kv)
			logLine("step %s %s", msg, b)
		}
	})

	s := &server{
		id: id, names: names, fsm: &sumFSM{node: id},
		props: make(chan *proposal), waiters: map[waitKey]*proposal{}, reads: make(chan *read),
		transfers: make(chan uint64, 4), confs: make(chan pb.ConfChangeI, 4), keep: voters[0],
	}
	s.status.Store(&status{State: "follower"})
	in := make(chan *pb.Message, 1024)
	unreachable := make(chan uint64, 64)
	// With SNAP_STATUS the transport says how each snapshot fared.
	var snapStatus chan snapResult
	if env("SNAP_STATUS", "") == "1" {
		snapStatus = make(chan snapResult, 64)
	}
	trans := newTransport(self, addrs, int(envUint("TRANSPORT_CONNS", 2)), in, unreachable, snapStatus)
	if err := trans.listen(raftBind); err != nil {
		fatal("listen raft: %v", err)
	}

	cfg := rawnode.Config{
		ID: self, Peers: voters, Name: func(n uint64) string { return names[n] },
		Disk: disk, Rep: sink, Send: trans.send, Apply: s.apply,
		State: func(role string, term uint64) { logLine("msg=raft-state role=%s term=%d", role, term) },
		// Defaults are slow, to keep the trace small: a tick is 100 ms, a
		// heartbeat every second, an election after 3 to 6 seconds.
		ElectionTick:  int(envUint("ELECTION_TICK", 30)),
		HeartbeatTick: int(envUint("HEARTBEAT_TICK", 10)),
		MaxSizePerMsg: envUint("MAX_SIZE_PER_MSG", 256),
		Boot:          env("BOOT_ENTRY", "1") == "1",
		PreVote:       env("PREVOTE", "") == "1",
		CheckQuorum:   env("CHECK_QUORUM", "") == "1",
		// ASYNC: raft's AsyncStorageWrites, with writes and applies on their
		// own goroutines. With ASYNC a request for votes waits for its write
		// (patches/README.md, E1) unless NO_HOLD_VOTE is set. PARALLEL: a leader
		// sends its requests before it writes.
		Async:      env("ASYNC", "") == "1",
		NoHoldVote: env("NO_HOLD_VOTE", "") == "1",
		Parallel:   env("PARALLEL", "") == "1",
		Logger:     logger,
		// FORWARD: a follower passes a proposal on to its leader (raft's
		// default, and what etcd does). MAX_INFLIGHT: raft's MaxInflightMsgs
		// (0: 256). SNAP_STATUS: raft is told whether each snapshot it sent
		// was written to its connection or lost. BATCH: the node takes one
		// Ready, and makes one write, for up to that many inputs when they
		// are waiting (0 or 1: a Ready after every input); BATCH_WAIT: it
		// first waits that long for more, as a node does whose last write
		// is still being made.
		Forward:     env("FORWARD", "") == "1",
		MaxInflight: int(envUint("MAX_INFLIGHT", 0)),
		SnapStatus:  env("SNAP_STATUS", "") == "1",
		Batch:       envUint("BATCH", 0) > 1,
		// STEP_DOWN: a leader that applies its own removal stops leading
		// (raft's StepDownOnRemoval).
		StepDown: env("STEP_DOWN", "") == "1",
	}
	s.forward = cfg.Forward
	s.readIndex = env("READ_INDEX", "") == "1"
	// SNAPSHOT_EVERY: the node puts a snapshot of the state machine in place
	// of its log every so many applied entries (0: never). A follower that
	// needs entries its leader no longer has is then sent the snapshot.
	s.snapEvery = envUint("SNAPSHOT_EVERY", 0)
	cfg.Restore = func(index uint64, data []byte) {
		var st fsmState
		if err := json.Unmarshal(data, &st); err != nil {
			fatal("snapshot: %v", err)
		}
		s.fsm.restore(st)
		s.applied.Store(index)
	}
	go s.run(cfg, envDuration("TICK", 100*time.Millisecond), int(envUint("BATCH", 0)), envDuration("BATCH_WAIT", 0), in, unreachable, snapStatus)

	mux := http.NewServeMux()
	mux.HandleFunc("POST /add", s.handleAdd)
	mux.HandleFunc("GET /sum", s.handleSum)
	mux.HandleFunc("GET /status", s.handleStatus)
	mux.HandleFunc("POST /transfer", s.handleTransfer)
	mux.HandleFunc("POST /conf", s.handleConf)
	srv := &http.Server{Addr: httpBind, Handler: mux, ReadHeaderTimeout: 5 * time.Second}
	go func() {
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			fatal("http: %v", err)
		}
	}()
	logLine("msg=raft-server-started node=%s", id)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGTERM, syscall.SIGINT)
	<-sig
	logLine("msg=raft-server-stopping node=%s", id)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	_ = srv.Shutdown(ctx)
}

// died is deferred on every goroutine that runs raft or its writes.
func (s *server) died() {
	if r := recover(); r != nil {
		// Raft panics when it finds its own state impossible.
		assert.Unreachable("raft does not panic", map[string]any{"node": s.id, "panic": fmt.Sprint(r)})
		logLine("msg=raft-panic node=%s panic=%q\n%s", s.id, fmt.Sprint(r), debug.Stack())
		os.Exit(2)
	}
}

// run is raft's goroutine: the only one that touches the node. With ASYNC,
// each write and each batch of entries to apply runs on a goroutine of its
// own, one write and one batch at a time, and comes back here when done.
//
// With BATCH, up to that many inputs that are waiting are handed to raft
// before its Ready is taken (node.Flush), as happens where raft runs behind
// a channel and its Ready is taken when the application is free.
func (s *server) run(cfg rawnode.Config, tick time.Duration, batch int, batchWait time.Duration, in <-chan *pb.Message, unreachable <-chan uint64, snapStatus <-chan snapResult) {
	defer s.died()
	// Reads waiting for their index. Only this goroutine touches the map; a
	// read nobody waits for any more is dropped at the next tick.
	waiting := map[uint64]*read{}
	cfg.Read = func(ctx []byte, index uint64) {
		if len(ctx) != 8 {
			return
		}
		id := binary.BigEndian.Uint64(ctx)
		if r := waiting[id]; r != nil {
			delete(waiting, id)
			go s.serve(r, index)
		}
	}
	// The configuration has changed since it was last published, or since
	// the last snapshot.
	// (A snapshot from a leader is put in place on another goroutine where
	// applying is.)
	var changed atomic.Bool
	changed.Store(true)
	snapDue := false
	cfg.Changed = func(uint64, *pb.ConfState) { changed.Store(true); snapDue = true }
	restore := cfg.Restore
	cfg.Restore = func(index uint64, data []byte) { restore(index, data); changed.Store(true) }
	node, err := rawnode.Start(cfg)
	if err != nil {
		fatal("start raft: %v", err)
	}
	var conf [3][]string
	// A leader that has applied its own removal goes on leading unless raft
	// is told to make it stop (STEP_DOWN), and takes no proposals: the node
	// then asks raft, every so many steps, to hand leadership to a voter
	// (patches/README.md, N6).
	var voterIDs []uint64
	idle := 0
	handOver := func() {
		st := node.Status()
		if st.RaftState != raft.StateLeader || len(voterIDs) == 0 {
			idle = 0
			return
		}
		for _, id := range voterIDs {
			if id == cfg.ID {
				idle = 0
				return
			}
		}
		if idle++; idle%20 == 1 {
			node.TransferLeader(voterIDs[(idle/20)%len(voterIDs)])
		}
	}
	publish := func() {
		if changed.Swap(false) {
			cs := node.Conf()
			voterIDs = cs.GetVoters()
			conf = [3][]string{s.namesOf(cs.GetVoters()), s.namesOf(cs.GetVotersOutgoing()), s.namesOf(cs.GetLearners())}
			logLine("msg=raft-conf voters=%s outgoing=%s learners=%s", strings.Join(conf[0], ","), strings.Join(conf[1], ","), strings.Join(conf[2], ","))
		}
		st := node.Status()
		s.status.Store(&status{
			State: strings.ToLower(strings.TrimPrefix(st.RaftState.String(), "State")), Term: st.GetTerm(),
			Leader: s.names[st.Lead], Commit: st.GetCommit(), Applied: st.Applied, LastIndex: node.LastIndex(),
			Voters: conf[0], Outgoing: conf[1], Learners: conf[2],
		})
	}
	publish()
	snapped := node.Applied()
	wrote := make(chan *rawnode.Write, 1)
	applied := make(chan *rawnode.Apply, 1)
	work := func() {
		if w := node.NextWrite(); w != nil {
			go func() { defer s.died(); node.RunWrite(w); wrote <- w }()
		}
		if a := node.NextApply(); a != nil {
			go func() { defer s.died(); node.RunApply(a); applied <- a }()
		}
	}
	work()
	ticker := time.NewTicker(tick)
	defer ticker.Stop()
	// input hands raft one input: the next one, or, if wait is false, one
	// that is waiting, if there is one.
	input := func(wait bool) bool {
		var idle chan struct{}
		if !wait {
			idle = make(chan struct{})
			close(idle)
		}
		select {
		case w := <-wrote:
			node.DoneWrite(w)
		case a := <-applied:
			node.DoneApply(a)
		case r := <-s.reads:
			waiting[r.id] = r
			node.ReadIndex(binary.BigEndian.AppendUint64(nil, r.id))
		case <-ticker.C:
			for id, r := range waiting {
				if time.Since(r.asked) > applyWait {
					delete(waiting, id)
				}
			}
			node.Tick()
		case m := <-in:
			node.Step(m)
		case id := <-unreachable:
			node.Unreachable(id)
		case r := <-snapStatus:
			if !r.ok {
				assert.Reachable("a leader is told that a snapshot it sent did not arrive", map[string]any{"node": s.id})
			}
			node.SnapshotStatus(r.to, r.ok)
		case to := <-s.transfers:
			node.TransferLeader(to)
		case cc := <-s.confs:
			_ = node.ProposeConfChange(cc)
		case p := <-s.props:
			// The waiter is there before raft has the entry: on a single
			// goroutine the entry cannot be applied before Propose returns,
			// but it can be before this case ends.
			key := waitKey{p.cmd.Kind, p.cmd.Op}
			s.mu.Lock()
			s.waiters[key] = p
			s.mu.Unlock()
			err := node.Propose(encodeCommand(p.cmd))
			if err != nil {
				s.forget(key)
			}
			p.proposed <- err
		case <-idle:
			return false
		}
		return true
	}
	for {
		input(true)
		if batch > 1 && batchWait > 0 {
			time.Sleep(batchWait)
		}
		for k := 1; k < batch && input(false); k++ {
		}
		node.Flush()
		// A snapshot is of the state machine as it is when nothing is being
		// applied: after an input's entries, or, with ASYNC, between two
		// batches (the node says no while one is being applied). One is
		// also taken after a change of membership: a node that the change
		// added does not take a snapshot from before it (patches/README.md, N5).
		if at := node.Applied(); s.snapEvery > 0 && (at >= snapped+s.snapEvery || snapDue && at > snapped) {
			data, _ := json.Marshal(s.fsm.state())
			if node.Snapshot(at, data) == nil {
				snapped, snapDue = at, false
			}
		}
		work()
		publish()
		handOver()
	}
}

func (s *server) forget(key waitKey) {
	s.mu.Lock()
	delete(s.waiters, key)
	s.mu.Unlock()
}

// serve answers a read once the state machine has applied up to its read
// index.
func (s *server) serve(r *read, index uint64) {
	for s.applied.Load() < index {
		if time.Since(r.asked) > applyWait {
			return
		}
		time.Sleep(time.Millisecond)
	}
	r.done <- s.fsm.state()
}

// readAt is a linearizable read through raft's ReadIndex, on any node: the
// state machine once it has applied everything committed when the read was
// asked for.
func (s *server) readAt() (fsmState, error) {
	r := &read{id: rand.Uint64(), asked: time.Now(), done: make(chan fsmState, 1)}
	deadline := time.After(applyWait)
	select {
	case s.reads <- r:
	case <-deadline:
		return fsmState{}, errUnknown
	}
	select {
	case st := <-r.done:
		return st, nil
	case <-deadline:
		return fsmState{}, errUnknown
	}
}

// apply is given every committed entry, in log order, by one goroutine at a
// time.
func (s *server) apply(e *pb.Entry) {
	defer s.applied.Store(e.GetIndex())
	if e.GetType() != pb.EntryNormal || len(e.GetData()) == 0 || (e.GetIndex() == 1 && string(e.GetData()) == string(rawnode.BootData)) {
		return // the entry a new leader starts its term with, or the log starts with
	}
	c, err := decodeCommand(e.GetData())
	if err != nil {
		assert.Unreachable("the state machine only receives well-formed commands",
			map[string]any{"node": s.id, "index": e.GetIndex(), "len": len(e.GetData())})
		return
	}
	var st fsmState
	if c.Kind == 'A' {
		st = s.fsm.apply(e.GetIndex(), e.GetTerm(), c)
	} else {
		st = s.fsm.state()
	}
	key := waitKey{c.Kind, c.Op}
	s.mu.Lock()
	p := s.waiters[key]
	delete(s.waiters, key)
	s.mu.Unlock()
	if p != nil {
		p.applied <- st
	}
}

const applyWait = 2 * time.Second

var (
	errNotLeader = errors.New("not leader")
	errUnknown   = errors.New("unknown")
)

// commit puts a command in the log and waits until this node has applied
// it. errNotLeader means it was never appended. errUnknown means it may or
// may not be committed, now or later.
//
// With FORWARD a node that does not lead and knows a leader takes the
// command too: raft passes it on, and this node answers when it has applied
// it. If the leader does not take it, the answer is errUnknown.
func (s *server) commit(c command) (fsmState, error) {
	if st := s.status.Load(); st.State != "leader" && !(s.forward && st.Leader != "") {
		return fsmState{}, errNotLeader
	}
	p := &proposal{cmd: c, proposed: make(chan error, 1), applied: make(chan fsmState, 1)}
	deadline := time.After(applyWait)
	select {
	case s.props <- p:
	case <-deadline:
		return fsmState{}, errNotLeader // raft never saw it
	}
	if err := <-p.proposed; err != nil {
		return fsmState{}, errNotLeader
	}
	select {
	case st := <-p.applied:
		return st, nil
	case <-deadline:
		s.forget(waitKey{c.Kind, c.Op})
		return fsmState{}, errUnknown
	}
}

func writeJSON(w http.ResponseWriter, code int, v any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(code)
	_ = json.NewEncoder(w).Encode(v)
}

func (s *server) commitError(w http.ResponseWriter, err error) {
	if errors.Is(err, errNotLeader) {
		writeJSON(w, http.StatusMisdirectedRequest, map[string]any{"error": "not_leader", "leader": s.status.Load().Leader})
		return
	}
	writeJSON(w, http.StatusGatewayTimeout, map[string]any{"error": "unknown", "detail": "timeout"})
}

func (s *server) handleAdd(w http.ResponseWriter, req *http.Request) {
	q := req.URL.Query()
	op, err1 := strconv.ParseUint(q.Get("op"), 10, 64)
	val, err2 := strconv.ParseInt(q.Get("value"), 10, 64)
	if err1 != nil || err2 != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_request"})
		return
	}
	st, err := s.commit(command{Kind: 'A', Op: op, Value: val})
	if err != nil {
		s.commitError(w, err)
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{"index": st.Index, "sum": st.Sum, "leader": s.status.Load().Leader})
}

// POST /transfer?to=NAME asks raft to hand leadership to that node. The
// answer says only that raft was asked.
func (s *server) handleTransfer(w http.ResponseWriter, req *http.Request) {
	to := req.URL.Query().Get("to")
	for id, name := range s.names {
		if name == to {
			select {
			case s.transfers <- id:
				writeJSON(w, http.StatusOK, map[string]any{"asked": to, "state": s.status.Load().State})
			default:
				writeJSON(w, http.StatusServiceUnavailable, map[string]any{"error": "busy"})
			}
			return
		}
	}
	writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_request"})
}

func (s *server) namesOf(ids []uint64) []string {
	out := make([]string, 0, len(ids))
	for _, id := range ids {
		out = append(out, s.names[id])
	}
	return out
}

// POST /conf asks raft for a change of membership. The answer says only that
// raft was asked: whether the change is appended, and when it is applied,
// shows in /status.
//
//	add=a,b remove=c learner=d   nodes to make voters, to remove, to make learners
//	mode=auto|implicit|explicit  auto (default): one node is changed in one step,
//	                             several by a joint change that raft leaves by
//	                             itself; implicit: a joint change always, left
//	                             by raft; explicit: a joint change that stays
//	                             until leave=1
//	leave=1                      leave the joint configuration
//	v1=1                         one node, as raft's older ConfChange
func (s *server) handleConf(w http.ResponseWriter, req *http.Request) {
	q := req.URL.Query()
	cc := &pb.ConfChangeV2{}
	bad := func() { writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_request"}) }
	for _, k := range []struct {
		key string
		typ pb.ConfChangeType
	}{{"add", pb.ConfChangeAddNode}, {"remove", pb.ConfChangeRemoveNode}, {"learner", pb.ConfChangeAddLearnerNode}} {
		for _, name := range strings.Split(q.Get(k.key), ",") {
			if name == "" {
				continue
			}
			var id uint64
			for n, have := range s.names {
				if have == name {
					id = n
				}
			}
			if id == 0 || (id == s.keep && k.typ != pb.ConfChangeAddNode) {
				bad()
				return
			}
			cc.Changes = append(cc.Changes, &pb.ConfChangeSingle{Type: k.typ.Enum(), NodeId: &id})
		}
	}
	switch q.Get("mode") {
	case "", "auto":
	case "implicit":
		cc.Transition = pb.ConfChangeTransitionJointImplicit.Enum()
	case "explicit":
		cc.Transition = pb.ConfChangeTransitionJointExplicit.Enum()
	default:
		bad()
		return
	}
	if (q.Get("leave") == "1") != (len(cc.Changes) == 0) || (q.Get("leave") == "1" && cc.Transition != nil) {
		bad()
		return
	}
	var change pb.ConfChangeI = cc
	if q.Get("v1") == "1" {
		if len(cc.Changes) != 1 || cc.Transition != nil {
			bad()
			return
		}
		change = &pb.ConfChange{Type: cc.Changes[0].Type, NodeId: cc.Changes[0].NodeId}
	}
	select {
	case s.confs <- change:
		writeJSON(w, http.StatusOK, map[string]any{"asked": true, "state": s.status.Load().State})
	default:
		writeJSON(w, http.StatusServiceUnavailable, map[string]any{"error": "busy"})
	}
}

// GET /sum?mode=linear (default) puts a read entry through the log first
// and answers with the state machine as it was when that entry was applied,
// so it is linearizable and only works on the leader. With READ_INDEX it
// asks raft for a read index instead and answers once the state machine has
// applied up to it; that works on any node that knows a leader. mode=stale reads the
// local state machine on any node.
func (s *server) handleSum(w http.ResponseWriter, req *http.Request) {
	var st fsmState
	switch req.URL.Query().Get("mode") {
	case "", "linear":
		var err error
		if s.readIndex {
			st, err = s.readAt()
		} else {
			st, err = s.commit(command{Kind: 'R', Op: rand.Uint64()})
		}
		if err != nil {
			s.commitError(w, err)
			return
		}
	case "stale":
		st = s.fsm.state()
	default:
		writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_mode"})
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{
		"node": s.id, "index": st.Index, "term": st.Term, "sum": st.Sum, "count": st.Count,
		"digest": strconv.FormatUint(st.Digest, 10),
	})
}

func (s *server) handleStatus(w http.ResponseWriter, req *http.Request) {
	st := s.status.Load()
	writeJSON(w, http.StatusOK, map[string]any{
		"node": s.id, "state": st.State, "term": st.Term, "leader": st.Leader,
		"commit": st.Commit, "applied": st.Applied, "last_index": st.LastIndex,
		"voters": st.Voters, "outgoing": st.Outgoing, "learners": st.Learners,
	})
}
