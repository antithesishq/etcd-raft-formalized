// Package rawnode runs one etcd-io/raft node (a RawNode) and reports every step
// it takes at raft's boundary: what it recovered, each write to its disk,
// each message it sends, each entry it hands to the state machine. Nothing
// here needs code inside raft. The server (../server) and the simulator
// (../sim) both run their nodes through this package, so they report the
// same steps.
//
// A Node belongs to one goroutine. After every input (a message, a tick, a
// proposal) it takes raft's Ready until there is none left, so every report
// follows from exactly one input. There are three ways it deals with a
// Ready.
//
// By default, for each Ready it
//
//  1. announces the write (the new HardState and entries) and makes it, as
//     one atomic Save;
//  2. sends the messages;
//  3. hands the committed entries to the state machine;
//
// in that order: nothing leaves the node before the state it was computed
// from is on disk.
//
// With Config.Parallel a node that leads sends its requests to append and
// its heartbeats first, and then does the same. Raft's contract allows a
// leader this (Ready.Messages in ../../node.go).
//
// With Config.Async raft runs with AsyncStorageWrites. The Node then only
// queues what a Ready asks to be written and applied, and sends at once
// the messages raft does not make wait for a write. The program takes the
// queued work when it chooses:
//
//	w := n.NextWrite()   // on the Node's goroutine; nil if there is none
//	n.RunWrite(w)        // anywhere: announces the write and makes it
//	n.DoneWrite(w)       // on the Node's goroutine: sends what waited for it
//
// and likewise NextApply, RunApply, DoneApply. Writes are made in order,
// one at a time.
//
// With Config.Batch the Node takes no Ready after an input. The program
// calls Flush when it wants raft's Ready taken, so one Ready, and one write,
// can follow from several inputs, as it does where raft runs behind a
// channel (raft's Node, etcd). After each input the Node reports what raft
// has in memory then (`mem`: role, term, vote, commit index, and, for a
// leader, the entries the input made it append). What a follower stored for
// a request to append is not reported there: raft does not show it before
// the Ready. At the Ready the Node reports `flush` once for each `mem` that
// is now written, then the write as a whole (`net`), makes it, reports
// that it is made (`made`), sends the messages, and reports `wrote`. A snapshot from a leader is handled
// alone: what is waiting is flushed first.
//
// Reports, and their fields:
//
//	boot    term, vote, commit, lastIndex, lastTerm     what was recovered
//	recv    msg                                         the message the next reports answer
//	ready   by, role, term, vote, commit, first, entries   what raft did, announced as a write
//	mem     by, role, term, vote, commit, first, entries, w   the same when the write comes
//	                                                    later (w = 1) or there is none (w = 0)
//	write   term, vote, commit, first, entries          the write of the oldest mem, announced
//	wrote                                               that write is made
//	flush   more                                        Batch: the oldest mem not yet written is
//	                                                    part of the write that comes next
//	                                                    (more = 1: the same write as the flush
//	                                                    before)
//	net     term, vote, commit, first, entries          Batch: that write as a whole, announced
//	made                                                Batch: it is on disk; `wrote` follows the
//	                                                    messages that waited for it
//	send    by, msg, b                                  Batch (b = 1): a message of a Ready that
//	                                                    followed from several inputs
//	send    by, msg                                     after the write
//	send    by, msg, cause                              Async: `cause` is the message it answers
//	                                                    ([] for none)
//	apply   by, first, entries                          before the state machine has them
//	                                                    (Async: with a = 1)
//	readreq ctx                                         the program asks for a read index
//	read    ctx, index                                  raft gives one (Config.Read is called)
//	snap    index, term                                 a snapshot of the state machine now stands
//	                                                    for the log up to index (Node.Snapshot)
//	restore index, voters, outgoing                     the state machine is replaced by a
//	                                                    snapshot a leader sent (Config.Restore)
//	conf    index, voters, outgoing                     raft is told that the change of membership
//	                                                    at index is applied (ApplyConfChange), and
//	                                                    counts with these voters from here on
//
// boot also has `applied`: the index of the snapshot the state machine starts
// from (0 for none), and the `voters` and `outgoing` voters raft starts with:
// those of that snapshot, or Config.Peers. A ready, mem or write whose write replaces the log by a
// snapshot a leader sent has snap = {index, term}; a `snap` message is
// reported with the snapshot's index and term as its index and logTerm.
//
// A node with an empty disk can first be given the entry every node's log
// starts with (Config.Boot); that write is not reported: it is the state the
// node starts in.
//
// `by` is the input the report follows from: "recv" (the last recv report
// of this node), "tick", "propose", "campaign", "transfer", "snapstatus",
// "read" or "boot". A message that
// changes nothing visible is not reported. A message is
// {type, from, to, term, index, logTerm, entries, commit, reject, hint};
// an entry is {term, type, value}.
//
// Membership. Every node is started with the same first voters
// (Config.Peers), whether it is one of them or not. A change is proposed
// with ProposeConfChange and is an entry of type "conf", whose value is
// {add, remove, joint, leave}: the nodes it makes voters, the nodes it makes
// not voters (removed, or learners), whether it is a joint change, and
// whether it leaves a joint configuration. When the node hands such an entry
// to its state machine it also tells raft (ApplyConfChange) and reports
// `conf`; with Async, when it tells raft that the entries are applied
// (DoneApply), on the Node's goroutine. A snapshot holds the configuration
// as of its index, and a node that restarts has that one.
package rawnode

import (
	"encoding/hex"
	"errors"
	"fmt"
	"log"
	"os"
	"sort"
	"strings"

	"google.golang.org/protobuf/proto"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// Reporter takes the reports. tracekit.Sink is one.
type Reporter interface {
	// Emit reports a step.
	Emit(msg string, kv ...any)
	// Do announces a durable write and then makes it.
	Do(fn func() error, msg string, kv ...any) error
}

// Config is what a Node is started with.
type Config struct {
	ID    uint64
	Peers []uint64            // the voters every node starts with
	Name  func(uint64) string // the name reports use for a node; "" for none
	Disk  Disk
	Rep   Reporter
	// Send is given each message after the write it depends on.
	Send func(*pb.Message)
	// Apply is given each committed entry, in order.
	Apply func(*pb.Entry)
	// State, if set, is called when the node's role changes.
	State func(role string, term uint64)
	// Restore, if set, is given a snapshot the state machine must be replaced
	// by: one this node took (at Start) or one a leader sent.
	Restore func(index uint64, data []byte)
	// Changed, if set, is called when raft has been told of a change of
	// membership: the index of its entry, and the configuration raft now
	// counts with. A program that takes snapshots takes one soon after: a
	// node refuses a snapshot whose voters and learners it is not among, so
	// a node that was added after the leader's last snapshot cannot be
	// brought up to date with that one (patches/README.md, N5).
	Changed func(index uint64, cs *pb.ConfState)
	// Read, if set, is given the index raft answers a ReadIndex with: the
	// state machine may be read for that request once it has applied up to
	// there.
	Read func(ctx []byte, index uint64)

	// Boot: a node with an empty disk first writes the entry every node's
	// log starts with (index 1, term 1), as a bootstrap would leave it.
	// Without it the log starts empty, at term 0.
	Boot bool

	// Split makes a Ready's state several writes instead of one, each
	// announced, so that a kill can fall between them:
	// "term-entries-commit", "hardstate-entries" or "entries-hardstate".
	Split string

	// Async runs raft with AsyncStorageWrites: see the package comment.
	Async bool
	// With Async, the node sends a request for votes after the write of
	// the Ready it came in, not at once: without that, raft as it is
	// upstream is not safe (patches/README.md, E1). NoHoldVote turns the hold off,
	// to show the fault, or to run raft with patches/E1, which makes the
	// request wait by itself.
	NoHoldVote bool
	// Parallel: without Async, a leader sends its requests to append and
	// its heartbeats before it writes.
	Parallel bool

	// Batch: a Ready is taken only when the program calls Flush, so it can
	// follow from several inputs: see the package comment. Not with Split or
	// Parallel.
	Batch bool
	// Forward: a follower passes a proposal on to its leader, as raft does
	// unless told not to. Without it a follower refuses a proposal.
	Forward bool
	// SnapStatus: the program tells the node how each snapshot it sent fared
	// (Node.SnapshotStatus), as raft asks an application to. Without it the
	// node tells raft at once that the snapshot arrived.
	SnapStatus bool

	ElectionTick  int
	HeartbeatTick int
	MaxSizePerMsg uint64
	// MaxInflight is raft's MaxInflightMsgs: how many requests to append a
	// leader may have sent to a follower and not had answered. 0: 256.
	MaxInflight int
	PreVote     bool
	CheckQuorum bool
	// StepDown is raft's StepDownOnRemoval: a leader that applies its own
	// removal stops leading.
	StepDown bool
	Logger   raft.Logger
}

// Node is one raft node and its disk.
type Node struct {
	cfg     Config
	rn      *raft.RawNode
	store   *store
	role    string
	hs      *pb.HardState // what is on disk
	cause   *pb.Message   // the message being handled, not reported yet
	causeTo uint64
	// The index of the last entry handed to the state machine, or of the
	// snapshot it was last replaced by.
	applied uint64

	// Batch: the reports of what raft did in memory (`mem` with w = 1) since
	// the last Ready.
	items int

	// Async, Batch.
	mhs *pb.HardState // what raft has in memory
	rhs *pb.HardState // the same as of the last Ready
	// Async.
	writes   []*Write // not made yet, oldest first
	inflight bool     // one has been taken and is not done
	applies  []*Apply
	applying bool
	// Writes queued or being made that replace the log by a snapshot a
	// leader sent.
	restoring int

	// The configurations raft was switched to since the snapshot on disk,
	// oldest first: a snapshot holds the one as of its index.
	confs []confAt
	// Batch: how many times raft, leading, has itself appended the entry that
	// leaves a joint configuration since the last report.
	autoLeft int
	// The index of the last snapshot a leader sent that raft was handed.
	// Raft has its configuration from then on, whatever is still waiting
	// to be applied.
	confBase uint64
}

// confAt is the configuration that the change at an index made.
type confAt struct {
	index uint64
	cs    *pb.ConfState
}

// Write is what one Ready asked to be written (raft's MsgStorageAppend),
// and the messages that wait for it.
type Write struct {
	hs     *pb.HardState // nil: none
	snap   *pb.Snapshot  // nil: none; otherwise the log is replaced by it
	ents   []*pb.Entry
	after  *pb.HardState // the HardState on disk after it
	resp   []*pb.Message
	cause  *pb.Message // the message the Ready answered
	by     string
	writes bool // there is something to write
	// Batch: how many `mem` reports the write is of; -1 otherwise.
	k int
}

// Restores says whether the write replaces the log by a snapshot a leader
// sent.
func (w *Write) Restores() bool { return w.snap != nil }

// Apply is the committed entries one Ready handed over (raft's
// MsgStorageApply).
type Apply struct {
	ents    []*pb.Entry
	restore *pb.Snapshot // instead of entries: replace the state machine
	resp    []*pb.Message
	by      string
}

// Start reports what is on the disk and starts raft on it.
func Start(cfg Config) (*Node, error) {
	hs, snap, ents, err := cfg.Disk.Load()
	if err != nil {
		return nil, err
	}
	if cfg.Boot && len(ents) == 0 && snap == nil && raft.IsEmptyHardState(hs) {
		hs = &pb.HardState{Term: new(uint64(1))}
		ents = []*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(1)), Data: BootData}}
		if err := cfg.Disk.Save(hs, ents); err != nil {
			return nil, err
		}
	}
	if cfg.Batch && (cfg.Split != "" || cfg.Parallel) {
		return nil, errors.New("kit: Batch with Split or Parallel")
	}
	n := &Node{cfg: cfg, store: &store{hs: hs, first: &pb.ConfState{Voters: cfg.Peers}, snap: snap, ents: ents}, role: "follower", hs: hs, mhs: hs, rhs: hs}
	n.applied = n.store.base()
	cs := n.store.conf()
	cfg.Rep.Emit("boot", "term", hs.GetTerm(), "vote", cfg.Name(hs.GetVote()), "commit", hs.GetCommit(),
		"lastIndex", n.store.last(), "lastTerm", n.store.lastTerm(), "applied", n.applied,
		"voters", n.names(cs.GetVoters()), "outgoing", n.names(cs.GetVotersOutgoing()))
	if snap != nil && cfg.Restore != nil {
		cfg.Restore(n.applied, snap.GetData())
	}
	inflight := cfg.MaxInflight
	if inflight == 0 {
		inflight = 256
	}
	n.rn, err = raft.NewRawNode(&raft.Config{
		ID:            cfg.ID,
		ElectionTick:  cfg.ElectionTick,
		HeartbeatTick: cfg.HeartbeatTick,
		Storage:       n.store,
		MaxSizePerMsg: cfg.MaxSizePerMsg,
		// Set, because raft takes MaxSizePerMsg for it when it is not, and
		// with MaxSizePerMsg 0 (one entry per message) then panics at its
		// first apply (patches/README.md, E2).
		MaxCommittedSizePerReady:  1 << 20,
		MaxInflightMsgs:           inflight,
		PreVote:                   cfg.PreVote,
		CheckQuorum:               cfg.CheckQuorum,
		StepDownOnRemoval:         cfg.StepDown,
		AsyncStorageWrites:        cfg.Async,
		Logger:                    n.logger(),
		DisableProposalForwarding: !cfg.Forward,
	})
	if err != nil {
		return nil, err
	}
	// A restarted node is handed its committed entries again here: the
	// state machine starts empty.
	n.drain("boot")
	n.alone()
	return n, nil
}

// Step hands raft a message from another node.
func (n *Node) Step(m *pb.Message) {
	if n.cfg.Batch && m.GetType() == pb.MsgSnap {
		// A snapshot from a leader is handled alone.
		n.Flush()
	}
	n.cause = m
	// Raft readdresses a message it passes on (a read index asked of a
	// follower goes to its leader) in place; the report is of the message as
	// it arrived.
	n.causeTo = m.GetTo()
	if n.cfg.Batch && m.GetType() == pb.MsgSnap {
		_ = n.rn.Step(m)
		n.drain("recv")
		n.alone()
		n.cause = nil
		return
	}
	err := n.rn.Step(m)
	var ents []*pb.Entry
	if err == nil && m.GetType() == pb.MsgProp {
		ents = m.GetEntries()
	}
	n.input("recv", ents)
	n.cause = nil
}

// input is called after raft has been handed an input. ents is what the
// input asked a leader to append, if raft did not refuse.
func (n *Node) input(by string, ents []*pb.Entry) {
	if !n.cfg.Batch {
		n.drain(by)
		return
	}
	n.note(by, ents)
}

// alone is called after a Ready was taken in a batching node as it is in
// one that does not batch (at the start, and for a snapshot from a leader).
func (n *Node) alone() {
	if !n.cfg.Batch {
		return
	}
	if !n.cfg.Async {
		n.mhs = n.hs
	}
	n.note("write", nil)
}

// note reports, in a batching node, what raft has in memory after an input,
// if the input changed it, or was a request to append.
func (n *Node) note(by string, ents []*pb.Entry) {
	st := n.rn.BasicStatus()
	hs := n.mhs
	if st.GetTerm() != hs.GetTerm() || st.GetVote() != hs.GetVote() || st.GetCommit() != hs.GetCommit() {
		hs = &pb.HardState{Term: new(st.GetTerm()), Vote: new(st.GetVote()), Commit: new(st.GetCommit())}
	}
	role := roleOf(st.RaftState)
	// What a leader appended: the empty entry its term starts with, or what
	// it was asked to and did not refuse.
	var app []*pb.Entry
	if role == "leader" {
		if n.role != "leader" {
			app = []*pb.Entry{{Term: new(st.GetTerm())}}
		} else {
			for _, e := range ents {
				app = append(app, &pb.Entry{Term: new(st.GetTerm()), Type: e.Type, Data: e.GetData()})
			}
			// What raft appended by itself: the entry that leaves a joint
			// configuration, when it applied the one that entered it.
			for ; n.autoLeft > 0; n.autoLeft-- {
				app = append(app, &pb.Entry{Term: new(st.GetTerm()), Type: pb.EntryConfChangeV2.Enum()})
			}
		}
	}
	n.autoLeft = 0
	m := n.cause
	request := m != nil && m.GetType() == pb.MsgApp && m.GetTerm() == st.GetTerm()
	if hs == n.mhs && role == n.role && !request && len(app) == 0 {
		return
	}
	w := 0
	if hs != n.mhs || request || len(app) > 0 {
		w = 1
	}
	kv := []any{"by", by, "role", role, "w", w, "term", hs.GetTerm(), "vote", n.cfg.Name(hs.GetVote()), "commit", hs.GetCommit()}
	if role == "leader" {
		kv = append(kv, "entries", n.entriesOf(app))
	}
	n.reportCause()
	n.cfg.Rep.Emit("mem", kv...)
	n.setRole(role, hs.GetTerm())
	n.mhs = hs
	n.items += w
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// flushes reports that the oldest k `mem` reports not yet written are part
// of one write, which follows.
func (n *Node) flushes(k int) {
	for j := range k {
		n.cfg.Rep.Emit("flush", "more", b2i(j > 0))
	}
}

// Flush takes raft's Ready, in a batching node: everything that followed
// from the inputs since the last one.
func (n *Node) Flush() {
	if !n.cfg.Batch {
		return
	}
	if n.cfg.Async {
		n.drainAsync("batch")
		if n.items > 0 {
			// Reports of something to write, and raft asked for no write.
			n.writes = append(n.writes, &Write{after: n.rhs, by: "batch", k: n.items})
			n.items = 0
		}
		return
	}
	for n.rn.HasReady() {
		rd := n.rn.Ready()
		if !raft.IsEmptySnap(rd.Snapshot) {
			panic("kit: a snapshot in a batch")
		}
		hs := n.hs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		write := hs != n.hs || len(rd.Entries) > 0
		k := n.items
		n.items = 0
		n.flushes(k)
		if write {
			var whs *pb.HardState
			if hs != n.hs {
				whs = hs
			}
			if err := n.cfg.Rep.Do(func() error { return n.cfg.Disk.Save(whs, rd.Entries) }, "net", n.state(hs, rd.Entries)...); err != nil {
				panic(fmt.Errorf("kit: write failed: %w", err))
			}
			n.store.save(whs, rd.Entries)
			n.hs = hs
		} else if k > 0 {
			n.cfg.Rep.Emit("net", n.state(hs, nil)...)
		}
		if k > 0 || write {
			n.cfg.Rep.Emit("made")
		}
		for _, m := range rd.Messages {
			n.cfg.Rep.Emit("send", "by", "batch", "msg", n.msgOf(m), "b", 1)
			n.cfg.Send(m)
		}
		if k > 0 || write {
			n.cfg.Rep.Emit("wrote")
		}
		n.reads(rd)
		if len(rd.CommittedEntries) > 0 {
			n.cfg.Rep.Emit("apply", "by", "batch", "first", rd.CommittedEntries[0].GetIndex(),
				"entries", n.entriesOf(rd.CommittedEntries))
			for _, e := range rd.CommittedEntries {
				n.cfg.Apply(e)
				n.switchConf(e)
			}
			n.applied = rd.CommittedEntries[len(rd.CommittedEntries)-1].GetIndex()
		}
		n.rn.Advance(rd)
		for _, m := range rd.Messages {
			n.sent(m)
		}
		// Raft takes note of its own write here: a leader's commit index
		// can move.
		n.note("write", nil)
	}
	if n.items > 0 {
		k := n.items
		n.items = 0
		n.flushes(k)
		n.cfg.Rep.Emit("net", n.state(n.hs, nil)...)
		n.cfg.Rep.Emit("made")
		n.cfg.Rep.Emit("wrote")
	}
}

// Tick moves raft's clock.
func (n *Node) Tick() {
	n.rn.Tick()
	n.input("tick", nil)
}

// Campaign makes the node start an election now.
func (n *Node) Campaign() {
	_ = n.rn.Campaign()
	n.input("campaign", nil)
}

// Propose asks raft to append an entry. An error means it was not appended.
// With Config.Forward, a follower that knows a leader passes the entry on
// to it and returns no error: the entry may or may not be appended.
func (n *Node) Propose(data []byte) error {
	err := n.rn.Propose(data)
	var ents []*pb.Entry
	if err == nil {
		ents = []*pb.Entry{{Data: data}}
	}
	n.input("propose", ents)
	return err
}

// ProposeConfChange asks raft to append a change of membership (a
// ConfChange or a ConfChangeV2). An error means nothing was appended. No
// error does not mean the change was: a leader that may not append it now
// (another change is not applied yet, or the change does not fit the
// configuration: joint or not) appends an empty entry in its place, and a
// follower passes it on as it does a proposal.
func (n *Node) ProposeConfChange(cc pb.ConfChangeI) error {
	typ, data, err := pb.MarshalConfChange(cc)
	if err != nil {
		return err
	}
	// What RawNode.ProposeConfChange does, with the message kept: raft puts
	// the entry it appends instead, if it does, in the message.
	m := &pb.Message{Type: pb.MsgProp.Enum(), From: new(n.cfg.ID), Entries: []*pb.Entry{{Type: typ.Enum(), Data: data}}}
	err = n.rn.Step(m)
	var ents []*pb.Entry
	if err == nil {
		ents = m.GetEntries()
	}
	n.input("propose", ents)
	return err
}

// Conf is the configuration raft counts with now.
func (n *Node) Conf() *pb.ConfState {
	cs := n.rn.Status().Config
	out := &pb.ConfState{Voters: cs.Voters[0].Slice(), VotersOutgoing: cs.Voters[1].Slice()}
	for id := range cs.Learners {
		out.Learners = append(out.Learners, id)
	}
	sort.Slice(out.Learners, func(i, j int) bool { return out.Learners[i] < out.Learners[j] })
	return out
}

// switchConf tells raft that a change of membership is applied, if e is
// one, and reports the configuration raft now counts with.
func (n *Node) switchConf(e *pb.Entry) {
	var cc pb.ConfChangeI
	switch e.GetType() {
	case pb.EntryConfChange:
		c := &pb.ConfChange{}
		if err := proto.Unmarshal(e.GetData(), c); err != nil {
			panic(err)
		}
		cc = c
	case pb.EntryConfChangeV2:
		c := &pb.ConfChangeV2{}
		if err := proto.Unmarshal(e.GetData(), c); err != nil {
			panic(err)
		}
		cc = c
	default:
		return
	}
	if e.GetIndex() <= n.confBase {
		// Raft has since been handed a snapshot that stands for this entry,
		// and has its configuration: telling it of the change now would
		// apply the change to that configuration (patches/README.md, N7).
		return
	}
	cs := n.rn.ApplyConfChange(cc)
	n.confs = append(n.confs, confAt{e.GetIndex(), cs})
	n.cfg.Rep.Emit("conf", "index", e.GetIndex(), "voters", n.names(cs.GetVoters()), "outgoing", n.names(cs.GetVotersOutgoing()))
	if n.cfg.Changed != nil {
		n.cfg.Changed(e.GetIndex(), cs)
	}
}

// confState is the configuration as of an index the node has applied.
func (n *Node) confState(index uint64) *pb.ConfState {
	cs := n.store.conf()
	for _, c := range n.confs {
		if c.index <= index {
			cs = c.cs
		}
	}
	return cs
}

func (n *Node) names(ids []uint64) []string {
	out := make([]string, 0, len(ids))
	for _, id := range ids {
		out = append(out, n.cfg.Name(id))
	}
	return out
}

// logger is the Logger raft is given. A batching node learns from it that
// raft, on its own, appended the entry that leaves a joint configuration:
// raft shows that nowhere else before the Ready.
func (n *Node) logger() raft.Logger {
	if !n.cfg.Batch {
		return n.cfg.Logger
	}
	l := n.cfg.Logger
	if l == nil {
		l = &raft.DefaultLogger{Logger: log.New(os.Stderr, "raft", log.LstdFlags)}
	}
	return autoLeave{l, n}
}

type autoLeave struct {
	raft.Logger
	n *Node
}

func (l autoLeave) Infof(format string, v ...any) {
	if strings.HasPrefix(format, "initiating automatic transition out of joint configuration") {
		l.n.autoLeft++
	}
	l.Logger.Infof(format, v...)
}

// ReadIndex asks raft for an index at which a read asked for now may be
// served (raft's ReadIndex, with ReadOnlySafe: the leader confirms that it
// still leads with a round of heartbeats). The answer, if one comes, is
// given to Config.Read with the same ctx.
func (n *Node) ReadIndex(ctx []byte) {
	n.cfg.Rep.Emit("readreq", "ctx", hex.EncodeToString(ctx))
	n.rn.ReadIndex(ctx)
	n.input("read", nil)
}

func (n *Node) reads(rd raft.Ready) {
	for _, rs := range rd.ReadStates {
		n.reportCause()
		n.cfg.Rep.Emit("read", "ctx", hex.EncodeToString(rs.RequestCtx), "index", rs.Index)
		if n.cfg.Read != nil {
			n.cfg.Read(rs.RequestCtx, rs.Index)
		}
	}
}

// Unreachable tells raft that a message to a peer could not be sent.
func (n *Node) Unreachable(id uint64) {
	n.rn.ReportUnreachable(id)
	n.input("tick", nil)
}

// TransferLeader asks raft to hand leadership to node `to`. A leader brings
// that node's log up to date and then tells it to start an election at once
// (MsgTimeoutNow); another node passes the request on to its leader.
func (n *Node) TransferLeader(to uint64) {
	n.rn.TransferLeader(to)
	n.input("transfer", nil)
}

// SnapshotStatus tells raft whether a snapshot sent to node `to` arrived
// (Config.SnapStatus). After a failure raft waits for that node's next
// answer to a heartbeat before it tries again.
func (n *Node) SnapshotStatus(to uint64, ok bool) {
	st := raft.SnapshotFinish
	if !ok {
		st = raft.SnapshotFailure
	}
	n.rn.ReportSnapshot(to, st)
	n.input("snapstatus", nil)
}

// Status is raft's view of itself.
func (n *Node) Status() raft.BasicStatus { return n.rn.BasicStatus() }

// LastIndex is the index of the last entry on disk.
func (n *Node) LastIndex() uint64 { return n.store.last() }

// Applied is the index of the last entry handed to the state machine, or of
// the snapshot it was last replaced by.
func (n *Node) Applied() uint64 { return n.applied }

// ErrNoSnapshot is what Snapshot returns when it may not put a snapshot at
// the index asked for.
var ErrNoSnapshot = errors.New("kit: no snapshot at that index")

// Snapshot puts a snapshot of the state machine, as it is after the entry
// at index, in place of the log up to there. The index must be one the
// state machine has reached, and within the commit index on disk: raft does
// not start on a snapshot beyond the commit index of its HardState. With
// Async, nothing may be being applied, or the state machine is not as it was
// after the entry at index; and no write that replaces the log by a
// snapshot a leader sent may be waiting or being made, or this snapshot,
// which is older, could reach the disk after it and stand for a log that is
// gone.
func (n *Node) Snapshot(index uint64, data []byte) error {
	if index <= n.store.base() || index > n.applied || index > n.hs.GetCommit() || n.applying || n.restoring > 0 {
		return ErrNoSnapshot
	}
	term, err := n.store.Term(index)
	if err != nil {
		return err
	}
	snap := &pb.Snapshot{Data: data, Metadata: &pb.SnapshotMetadata{
		Index: new(index), Term: new(term), ConfState: n.confState(index)}}
	n.cfg.Rep.Emit("snap", "index", index, "term", term)
	if err := n.cfg.Disk.SaveSnapshot(snap, nil, false); err != nil {
		panic(fmt.Errorf("kit: write failed: %w", err))
	}
	n.store.compact(snap)
	n.forget(index)
	return nil
}

// forget drops the configurations a snapshot at index now holds.
func (n *Node) forget(index uint64) {
	k := 0
	for k < len(n.confs) && n.confs[k].index <= index {
		k++
	}
	n.confs = n.confs[k:]
}

func snapOf(s *pb.Snapshot) map[string]any {
	return map[string]any{"index": s.GetMetadata().GetIndex(), "term": s.GetMetadata().GetTerm()}
}

// sent is called for every message handed to Config.Send. Raft waits to be
// told how a snapshot it sent fared; unless the program does that
// (Config.SnapStatus) it is told that it arrived, and finds out from the
// follower's replies if it did not.
func (n *Node) sent(m *pb.Message) {
	if m.GetType() == pb.MsgSnap && !n.cfg.SnapStatus {
		n.rn.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
	}
}

func roleOf(s raft.StateType) string {
	switch s {
	case raft.StateLeader:
		return "leader"
	case raft.StateCandidate:
		return "candidate"
	case raft.StatePreCandidate:
		return "precandidate"
	}
	return "follower"
}

func (n *Node) drain(by string) {
	if n.cfg.Async {
		n.drainAsync(by)
		return
	}
	for n.rn.HasReady() {
		rd := n.rn.Ready()
		role := n.role
		if rd.SoftState != nil {
			role = roleOf(rd.SoftState.RaftState)
		}
		hs := n.hs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		write := hs != n.hs || len(rd.Entries) > 0
		early := n.cfg.Parallel && role == "leader"
		if !raft.IsEmptySnap(rd.Snapshot) {
			// The log is replaced by a snapshot a leader sent: one write, and
			// then the state machine.
			if len(rd.Entries) > 0 {
				panic("kit: a Ready with a snapshot and entries")
			}
			n.reportCause()
			var whs *pb.HardState
			if hs != n.hs {
				whs = hs
			}
			kv := append([]any{"by", by, "role", role, "snap", snapOf(rd.Snapshot)}, n.state(hs, nil)...)
			if err := n.cfg.Rep.Do(func() error { return n.cfg.Disk.SaveSnapshot(rd.Snapshot, whs, true) }, "ready", kv...); err != nil {
				panic(fmt.Errorf("kit: write failed: %w", err))
			}
			n.store.restore(rd.Snapshot)
			n.confBase = rd.Snapshot.GetMetadata().GetIndex()
			n.confs = nil
			n.store.save(whs, nil)
			n.hs = hs
			n.setRole(role, hs.GetTerm())
			n.restored(rd.Snapshot, false)
			n.applied = rd.Snapshot.GetMetadata().GetIndex()
		} else if early {
			n.parallel(by, role, hs, rd)
		} else if write || role != n.role {
			n.reportCause()
			if write {
				for _, p := range n.parts(hs, rd.Entries) {
					kv := append([]any{"by", by, "role", role}, n.state(p.after, p.ents)...)
					if err := n.cfg.Rep.Do(func() error { return n.cfg.Disk.Save(p.hs, p.ents) }, "ready", kv...); err != nil {
						panic(fmt.Errorf("kit: write failed: %w", err))
					}
					n.store.save(p.hs, p.ents)
					n.hs = p.after
				}
			} else {
				n.cfg.Rep.Emit("ready", append([]any{"by", by, "role", role}, n.state(hs, nil)...)...)
			}
			n.setRole(role, hs.GetTerm())
		}
		for _, m := range rd.Messages {
			if early && isRequest(m) {
				continue // sent already
			}
			n.reportCause()
			n.cfg.Rep.Emit("send", "by", by, "msg", n.msgOf(m))
			n.cfg.Send(m)
		}
		n.reads(rd)
		if len(rd.CommittedEntries) > 0 {
			n.reportCause()
			n.cfg.Rep.Emit("apply", "by", by, "first", rd.CommittedEntries[0].GetIndex(),
				"entries", n.entriesOf(rd.CommittedEntries))
			for _, e := range rd.CommittedEntries {
				n.cfg.Apply(e)
				n.switchConf(e)
			}
			n.applied = rd.CommittedEntries[len(rd.CommittedEntries)-1].GetIndex()
		}
		n.rn.Advance(rd)
		for _, m := range rd.Messages {
			n.sent(m)
		}
	}
}

// restored replaces the state machine by a snapshot and reports it.
func (n *Node) restored(snap *pb.Snapshot, later bool) {
	index := snap.GetMetadata().GetIndex()
	cs := snap.GetMetadata().GetConfState()
	kv := []any{"index", index, "voters", n.names(cs.GetVoters()), "outgoing", n.names(cs.GetVotersOutgoing())}
	if later {
		kv = append(kv, "a", 1)
	}
	n.cfg.Rep.Emit("restore", kv...)
	if n.cfg.Restore != nil {
		n.cfg.Restore(index, snap.GetData())
	}
}

func isRequest(m *pb.Message) bool {
	return m.GetType() == pb.MsgApp || m.GetType() == pb.MsgHeartbeat
}

func first(ents []*pb.Entry) uint64 {
	if len(ents) == 0 {
		return 0
	}
	return ents[0].GetIndex()
}

// state is the fields of a report that say what raft has in memory, or what
// is on disk after a write.
func (n *Node) state(hs *pb.HardState, ents []*pb.Entry) []any {
	return []any{"term", hs.GetTerm(), "vote", n.cfg.Name(hs.GetVote()), "commit", hs.GetCommit(),
		"first", first(ents), "entries", n.entriesOf(ents)}
}

func (n *Node) setRole(role string, term uint64) {
	if role != n.role {
		n.role = role
		if n.cfg.State != nil {
			n.cfg.State(role, term)
		}
	}
}

// parallel is a leader's Ready with Config.Parallel, up to its write: the
// report of what raft did, the requests, and then the write.
func (n *Node) parallel(by, role string, hs *pb.HardState, rd raft.Ready) {
	write := hs != n.hs || len(rd.Entries) > 0
	w := 0
	if write {
		w = 1
	}
	if write || role != n.role {
		n.reportCause()
		n.cfg.Rep.Emit("mem", append([]any{"by", by, "role", role, "w", w}, n.state(hs, rd.Entries)...)...)
	}
	n.setRole(role, hs.GetTerm())
	for _, m := range rd.Messages {
		if isRequest(m) {
			n.reportCause()
			n.cfg.Rep.Emit("send", "by", by, "msg", n.msgOf(m))
			n.cfg.Send(m)
		}
	}
	if write {
		var whs *pb.HardState
		if hs != n.hs {
			whs = hs
		}
		n.cfg.Rep.Emit("write", n.state(hs, rd.Entries)...)
		if err := n.cfg.Disk.Save(whs, rd.Entries); err != nil {
			panic(fmt.Errorf("kit: write failed: %w", err))
		}
		n.cfg.Rep.Emit("wrote")
		n.store.save(whs, rd.Entries)
		n.hs = hs
	}
}

// drainAsync takes raft's Ready with AsyncStorageWrites: it reports what
// raft did in memory, queues the write and the entries to apply, and sends
// what does not wait.
func (n *Node) drainAsync(by string) {
	// A batching node has reported what raft did in memory already, input by
	// input (note); a snapshot from a leader is handled as in a node that
	// does not batch.
	batch := n.cfg.Batch && by == "batch"
	for n.rn.HasReady() {
		rd := n.rn.Ready()
		var snap *pb.Snapshot
		if !raft.IsEmptySnap(rd.Snapshot) {
			if len(rd.Entries) > 0 {
				panic("kit: a Ready with a snapshot and entries")
			}
			snap = rd.Snapshot
			n.confBase = snap.GetMetadata().GetIndex()
		}
		role := n.role
		if rd.SoftState != nil {
			role = roleOf(rd.SoftState.RaftState)
		}
		hs := n.rhs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		var app, apl *pb.Message
		var out []*pb.Message
		for _, m := range rd.Messages {
			switch m.GetTo() {
			case raft.LocalAppendThread:
				app = m
			case raft.LocalApplyThread:
				apl = m
			default:
				out = append(out, m)
			}
		}
		cause := n.cause
		write := hs != n.rhs || len(rd.Entries) > 0 || snap != nil
		if write && app == nil {
			panic("kit: raft changed its state and asked for no write")
		}
		if batch && snap != nil {
			panic("kit: a snapshot in a batch")
		}
		if !batch && (write || role != n.role) {
			w := 0
			if write {
				w = 1
			}
			kv := append([]any{"by", by, "role", role, "w", w}, n.state(hs, rd.Entries)...)
			if snap != nil {
				kv = append(kv, "snap", snapOf(snap))
			}
			n.reportCause()
			n.cfg.Rep.Emit("mem", kv...)
		}
		if !batch {
			n.setRole(role, hs.GetTerm())
		}
		var job *Write
		if app != nil {
			job = &Write{ents: rd.Entries, snap: snap, after: hs, resp: app.GetResponses(), cause: cause, by: by, writes: write, k: -1}
			if batch {
				job.k = n.items
				n.items = 0
			}
			if snap != nil {
				n.restoring++
			}
			if hs != n.rhs {
				job.hs = hs
			}
			n.writes = append(n.writes, job)
		}
		n.rhs = hs
		if !batch {
			n.mhs = hs
		}
		for _, m := range out {
			if !n.cfg.NoHoldVote && m.GetType() == pb.MsgVote && job != nil {
				job.resp = append(job.resp, m)
				continue
			}
			if batch {
				n.cfg.Rep.Emit("send", "by", by, "msg", n.msgOf(m), "b", 1)
			} else {
				n.reportCause()
				n.cfg.Rep.Emit("send", "by", by, "msg", n.msgOf(m), "cause", n.causeOf(cause))
			}
			n.cfg.Send(m)
			n.sent(m)
		}
		n.reads(rd)
		if apl != nil {
			n.applies = append(n.applies, &Apply{ents: apl.GetEntries(), resp: apl.GetResponses(), by: by})
		}
	}
}

func (n *Node) causeOf(m *pb.Message) []map[string]any {
	if m == nil {
		return []map[string]any{}
	}
	return []map[string]any{n.arrived(m)}
}

// arrived is the report of a message this node was handed: it was to this
// node.
func (n *Node) arrived(m *pb.Message) map[string]any {
	r := n.msgOf(m)
	r["to"] = n.cfg.Name(n.cfg.ID)
	return r
}

// Pending is how many writes and how many batches of entries to apply are
// queued.
func (n *Node) Pending() (writes, applies int) { return len(n.writes), len(n.applies) }

// NextWrite takes the oldest queued write, or returns nil if there is none
// or one is still being made.
func (n *Node) NextWrite() *Write {
	if n.inflight || len(n.writes) == 0 {
		return nil
	}
	w := n.writes[0]
	n.writes = n.writes[1:]
	n.inflight = true
	return w
}

// RunWrite announces the write and makes it. It touches nothing of the
// Node but its disk, and may run on another goroutine.
func (n *Node) RunWrite(w *Write) {
	if w.k >= 0 {
		n.flushes(w.k)
		if w.writes {
			if err := n.cfg.Rep.Do(func() error { return n.cfg.Disk.Save(w.hs, w.ents) }, "net", n.state(w.after, w.ents)...); err != nil {
				panic(fmt.Errorf("kit: write failed: %w", err))
			}
		} else if w.k > 0 {
			n.cfg.Rep.Emit("net", n.state(w.after, nil)...)
		}
		if w.k > 0 || w.writes {
			n.cfg.Rep.Emit("made")
		}
		return
	}
	if !w.writes {
		return
	}
	kv := n.state(w.after, w.ents)
	var err error
	if w.snap != nil {
		n.cfg.Rep.Emit("write", append(kv, "snap", snapOf(w.snap))...)
		err = n.cfg.Disk.SaveSnapshot(w.snap, w.hs, true)
	} else {
		n.cfg.Rep.Emit("write", kv...)
		err = n.cfg.Disk.Save(w.hs, w.ents)
	}
	if err != nil {
		panic(fmt.Errorf("kit: write failed: %w", err))
	}
	n.cfg.Rep.Emit("wrote")
}

// DoneWrite sends the messages that waited for the write and tells raft it
// is made.
func (n *Node) DoneWrite(w *Write) {
	if w.writes {
		if w.snap != nil {
			// The state machine is replaced after what it was handed before,
			// and before what raft hands it next.
			n.restoring--
			n.store.restore(w.snap)
			n.confs = nil
			n.applies = append(n.applies, &Apply{restore: w.snap, by: w.by})
		}
		n.store.save(w.hs, w.ents)
		n.hs = w.after
	}
	n.inflight = false
	for _, m := range w.resp {
		if m.GetTo() == n.cfg.ID {
			continue
		}
		if w.k >= 0 {
			n.cfg.Rep.Emit("send", "by", w.by, "msg", n.msgOf(m), "b", 1)
		} else {
			n.cfg.Rep.Emit("send", "by", w.by, "msg", n.msgOf(m), "cause", n.causeOf(w.cause))
		}
		n.cfg.Send(m)
	}
	if w.k > 0 || (w.k == 0 && w.writes) {
		n.cfg.Rep.Emit("wrote")
	}
	for _, m := range w.resp {
		if m.GetTo() == n.cfg.ID {
			_ = n.rn.Step(m)
		}
	}
	if n.cfg.Batch {
		n.note("write", nil)
		return
	}
	n.drainAsync("write")
}

// NextApply takes the oldest queued batch of committed entries, or returns
// nil if there is none or one is still being applied.
func (n *Node) NextApply() *Apply {
	if n.applying || len(n.applies) == 0 {
		return nil
	}
	a := n.applies[0]
	n.applies = n.applies[1:]
	n.applying = true
	return a
}

// RunApply hands the entries to the state machine. It may run on another
// goroutine.
func (n *Node) RunApply(a *Apply) {
	if a.restore != nil {
		n.restored(a.restore, true)
		return
	}
	if len(a.ents) == 0 {
		return
	}
	n.cfg.Rep.Emit("apply", "by", a.by, "first", a.ents[0].GetIndex(), "entries", n.entriesOf(a.ents), "a", 1)
	for _, e := range a.ents {
		n.cfg.Apply(e)
	}
}

// DoneApply tells raft the entries are applied, after telling it of each
// change of membership among them.
func (n *Node) DoneApply(a *Apply) {
	n.applying = false
	if a.restore != nil {
		n.applied = a.restore.GetMetadata().GetIndex()
	} else if len(a.ents) > 0 {
		n.applied = a.ents[len(a.ents)-1].GetIndex()
		for _, e := range a.ents {
			n.switchConf(e)
		}
	}
	for _, m := range a.resp {
		_ = n.rn.Step(m)
	}
	if n.cfg.Batch {
		n.note("apply", nil)
		return
	}
	n.drainAsync("apply")
}

// part is one write: a HardState (nil for none) and entries, and the
// HardState on disk after it.
type part struct {
	hs    *pb.HardState
	ents  []*pb.Entry
	after *pb.HardState
}

// parts is the writes a Ready's state is made in: one, or several in the
// order Config.Split names.
func (n *Node) parts(hs *pb.HardState, ents []*pb.Entry) []part {
	changed := hs != n.hs
	var w *pb.HardState
	if changed {
		w = hs
	}
	var out []part
	switch n.cfg.Split {
	case "term-entries-commit":
		// The term and the vote with the old commit index, then the
		// entries, then the commit index.
		cur := n.hs
		if hs.GetTerm() != cur.GetTerm() || hs.GetVote() != cur.GetVote() {
			tv := &pb.HardState{Term: hs.Term, Vote: hs.Vote, Commit: new(cur.GetCommit())}
			out = append(out, part{tv, nil, tv})
			cur = tv
		}
		if len(ents) > 0 {
			out = append(out, part{nil, ents, cur})
		}
		if hs.GetCommit() != cur.GetCommit() {
			out = append(out, part{hs, nil, hs})
		}
	case "hardstate-entries":
		if changed {
			out = append(out, part{hs, nil, hs})
		}
		if len(ents) > 0 {
			out = append(out, part{nil, ents, hs})
		}
	case "entries-hardstate":
		if len(ents) > 0 {
			out = append(out, part{nil, ents, n.hs})
		}
		if changed {
			out = append(out, part{hs, nil, hs})
		}
	default:
		out = append(out, part{w, ents, hs})
	}
	return out
}

// reportCause reports the message being handled, once, before the first
// report that follows from it.
func (n *Node) reportCause() {
	if n.cause != nil {
		n.cfg.Rep.Emit("recv", "msg", n.arrived(n.cause))
		n.cause = nil
	}
}

// BootData is what the entry every log starts with holds.
var BootData = []byte("boot")

func (n *Node) entryOf(e *pb.Entry) map[string]any {
	switch {
	case e.GetIndex() == 1 && string(e.GetData()) == string(BootData):
		return map[string]any{"term": e.GetTerm(), "type": "config", "value": ""}
	case e.GetType() != pb.EntryNormal:
		return map[string]any{"term": e.GetTerm(), "type": "conf", "value": n.changeOf(e)}
	case len(e.GetData()) == 0:
		return map[string]any{"term": e.GetTerm(), "type": "noop", "value": ""}
	}
	return map[string]any{"term": e.GetTerm(), "type": "command", "value": hex.EncodeToString(e.GetData())}
}

// changeOf is what a change of membership does to the voters: the nodes it
// makes voters (`add`), the nodes it makes not voters, by removing them or
// making them learners (`remove`), each in the order of their ids; whether
// it is a joint change; and whether it leaves a joint configuration.
func (n *Node) changeOf(e *pb.Entry) map[string]any {
	c := &pb.ConfChangeV2{}
	if e.GetType() == pb.EntryConfChange {
		c1 := &pb.ConfChange{}
		if err := proto.Unmarshal(e.GetData(), c1); err != nil {
			panic(err)
		}
		c = c1.AsV2()
	} else if err := proto.Unmarshal(e.GetData(), c); err != nil {
		panic(err)
	}
	voter := map[uint64]bool{}
	for _, ch := range c.GetChanges() {
		if id := ch.GetNodeId(); id != 0 && ch.GetType() != pb.ConfChangeUpdateNode {
			voter[id] = ch.GetType() == pb.ConfChangeAddNode
		}
	}
	var ids []uint64
	for id := range voter {
		ids = append(ids, id)
	}
	sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
	add, remove := []string{}, []string{}
	for _, id := range ids {
		if voter[id] {
			add = append(add, n.cfg.Name(id))
		} else {
			remove = append(remove, n.cfg.Name(id))
		}
	}
	_, joint := c.EnterJoint()
	return map[string]any{"add": add, "remove": remove, "joint": joint, "leave": c.LeaveJoint()}
}

func (n *Node) entriesOf(es []*pb.Entry) []map[string]any {
	out := make([]map[string]any, 0, len(es))
	for _, e := range es {
		out = append(out, n.entryOf(e))
	}
	return out
}

var msgTypes = map[pb.MessageType]string{
	pb.MsgApp: "app", pb.MsgAppResp: "appresp", pb.MsgVote: "vote", pb.MsgVoteResp: "voteresp",
	pb.MsgHeartbeat: "hb", pb.MsgHeartbeatResp: "hbresp", pb.MsgPreVote: "prevote", pb.MsgPreVoteResp: "prevoteresp",
	pb.MsgSnap: "snap", pb.MsgTimeoutNow: "timeoutnow", pb.MsgReadIndex: "readindex", pb.MsgReadIndexResp: "readindexresp",
	pb.MsgProp: "prop", pb.MsgTransferLeader: "transfer",
}

func (n *Node) msgOf(m *pb.Message) map[string]any {
	ty, ok := msgTypes[m.GetType()]
	if !ok {
		ty = m.GetType().String()
	}
	index, logTerm := m.GetIndex(), m.GetLogTerm()
	if m.GetType() == pb.MsgSnap {
		index, logTerm = m.GetSnapshot().GetMetadata().GetIndex(), m.GetSnapshot().GetMetadata().GetTerm()
	}
	return map[string]any{
		"type": ty, "from": n.cfg.Name(m.GetFrom()), "to": n.cfg.Name(m.GetTo()), "term": m.GetTerm(),
		"index": index, "logTerm": logTerm, "entries": n.entriesOf(m.GetEntries()),
		"commit": m.GetCommit(), "reject": m.GetReject(), "hint": m.GetRejectHint(),
	}
}
