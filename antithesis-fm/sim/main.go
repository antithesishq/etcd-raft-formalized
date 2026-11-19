// sim runs a cluster of etcd-io/raft nodes in one process, from a seed, and
// writes the steps they report as one stream, in the format the driver's
// collector writes (../../tracekit/driver/trace.rs). There is no real time,
// network or disk: the simulator chooses which message is delivered next,
// which is lost or delivered twice, when a node ticks, campaigns, is given
// a proposal, is cut off, or is killed, at any report, including between
// the announcement of a write and the write.
//
// With -member the membership changes: only the first -voters nodes are
// voters at the start, and nodes are asked to add and remove voters and
// learners, one at a time or several at once (a joint change), and to leave
// a joint configuration. One of the first voters, chosen by the seed, is
// never removed, so that no change removes every voter (raft panics when
// it applies one that does).
//
// With -async raft runs with AsyncStorageWrites, and when a node makes its
// next queued write, when the messages that waited for it leave, and when
// committed entries are applied are the simulator's choices too.
//
// The nodes run through package rawnode, as the server's do, so what a node
// reports here is what it would report there.
//
//	sim -seed 7 -nodes 3 -steps 2000 -out stream.ndjson
//
// Besides the stream it checks, on its own, that no two nodes apply
// different entries at one index. Exit status: 0 the run ended; 3 raft
// panicked or two nodes applied different entries (the stream up to there
// is written).
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"

	"google.golang.org/protobuf/proto"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"

	"etcd-raft-formalized/rawnode"
)

// killed is what a report panics with when the simulator kills the node
// there.
type killed struct{}

type sim struct {
	rng    *rand.Rand
	out    *json.Encoder
	k      int
	n      int
	nodes  []*rawnode.Node // nil: down
	disks  []*rawnode.MemDisk
	fuse   []int  // reports until the node is killed; 0: no kill planned
	cut    []bool // messages to and from the node wait
	net    []*pb.Message
	value  uint64
	logger raft.Logger
	boot   bool
	// With PreVote and CheckQuorum on, elections are raft's own: every node
	// ticks, and a node starts an election at a timeout raft draws for
	// itself, so a seed does not fix the run.
	strict bool
	// PreVote; CheckQuorum (both need strict).
	prevote, checkQuorum bool
	// Nodes are asked to hand leadership over; followers pass proposals on;
	// leaders are told how each snapshot they sent fared; MaxInflightMsgs.
	transfer, forward, snapStatus bool
	inflight                      int
	// Nodes take one Ready for several inputs: the simulator chooses when.
	batch   bool
	dirty   []bool // the node has been given input since its last Ready
	flushed bool   // this step was a node taking its Ready
	// A node with input takes its Ready at a step with odds one in this
	// many: 2, 5 or 8, chosen by the seed.
	flushOdds int
	split     string
	// AsyncStorageWrites; with it, do not hold a request for votes until
	// its write is made; a leader sends before it writes.
	async, nohold, parallel bool
	snaps                   bool // nodes take snapshots, so leaders send them
	// With -async: steps for which a node's disk does nothing (its queued
	// writes wait while the node goes on).
	stall   []int
	snapAt  []uint64 // where each node last took a snapshot
	reads   bool     // the simulator also asks nodes for read indexes
	readCtx uint64
	wip     []*rawnode.Write // made, and what waited for it not sent yet
	aip     []*rawnode.Apply // applied, and raft not told yet
	// The size limit of a request: one entry (0), a few entries, or no limit,
	// chosen by the seed.
	maxSize uint64
	// Membership changes are proposed; how many nodes are voters at the
	// start; the voter that is never removed; a leader that applies its own
	// removal steps down.
	member   bool
	calm     int // kills and cuts are this many times rarer
	voters   int
	anchor   uint64
	stepDown bool
	// With -snap: the node has applied a change of membership and takes a
	// snapshot at its next step.
	snapDue []bool

	applied map[uint64]string // index -> entry, as first applied by any node
	failure string
}

func name(id uint64) string {
	if id == 0 {
		return ""
	}
	return fmt.Sprintf("raft%d", id)
}

// reporter writes one node's reports to the stream.
type reporter struct {
	s  *sim
	id int
}

func (r reporter) Emit(msg string, kv ...any) {
	s := r.s
	// A kill lands before a report: the step was not taken.
	if s.fuse[r.id] > 0 {
		if s.fuse[r.id]--; s.fuse[r.id] == 0 {
			panic(killed{})
		}
	}
	ev := map[string]any{"e": msg, "node": name(uint64(r.id + 1))}
	for i := 0; i+1 < len(kv); i += 2 {
		ev[fmt.Sprint(kv[i])] = kv[i+1]
	}
	s.k++
	ev["k"] = s.k
	if err := s.out.Encode(ev); err != nil {
		panic(err)
	}
	// A kill can also land between the announcement of a write and the
	// write.
	if msg == "write" && s.fuse[r.id] == 1 && s.rng.IntN(2) == 0 {
		s.fuse[r.id] = 0
		panic(killed{})
	}
}

func (r reporter) Do(fn func() error, msg string, kv ...any) error {
	r.Emit(msg, kv...)
	// A kill can also land between the announcement and the write.
	if r.s.fuse[r.id] == 1 && r.s.rng.IntN(2) == 0 {
		r.s.fuse[r.id] = 0
		panic(killed{})
	}
	return fn()
}

func (s *sim) start(i int) {
	id := uint64(i + 1)
	peers := make([]uint64, s.voters)
	for j := range peers {
		peers[j] = uint64(j + 1)
	}
	s.guard(i, func() {
		n, err := rawnode.Start(rawnode.Config{
			ID: id, Peers: peers, Name: name, Disk: s.disks[i], Rep: reporter{s, i},
			Send: func(m *pb.Message) { s.net = append(s.net, proto.Clone(m).(*pb.Message)) },
			Apply: func(e *pb.Entry) {
				got := fmt.Sprintf("%d/%x", e.GetTerm(), e.GetData())
				if was, ok := s.applied[e.GetIndex()]; ok && was != got {
					s.failure = fmt.Sprintf("DIVERGED at index %d: %s applied %s, another node %s", e.GetIndex(), name(id), got, was)
				}
				s.applied[e.GetIndex()] = got
			},
			// Elections are started by the simulator, never by a timeout,
			// unless PreVote and CheckQuorum are on.
			Async: s.async, NoHoldVote: s.nohold, Parallel: s.parallel,
			Boot: s.boot, Split: s.split, ElectionTick: s.electionTick(), HeartbeatTick: 1, PreVote: s.prevote, CheckQuorum: s.checkQuorum, MaxSizePerMsg: s.maxSize, Logger: s.logger,
			Batch: s.batch, Forward: s.forward, SnapStatus: s.snapStatus, MaxInflight: s.inflight, StepDown: s.stepDown,
			Changed: func(uint64, *pb.ConfState) { s.snapDue[i] = s.snaps },
		})
		if err != nil {
			panic(err)
		}
		s.nodes[i] = n
	})
}

// guard runs one step of node i. If the simulator kills the node during it,
// the node is down afterwards, with its disk as it was at that moment.
func (s *sim) guard(i int, step func()) {
	defer func() {
		if r := recover(); r != nil {
			s.fuse[i] = 0
			s.nodes[i] = nil
			s.wip[i], s.aip[i] = nil, nil
			s.snapDue[i] = false
			s.stall[i] = 0
			s.dirty[i] = false
			if _, ok := r.(killed); !ok {
				s.failure = fmt.Sprintf("PANIC in %s: %v", name(uint64(i+1)), r)
			}
		}
	}()
	step()
	if s.batch && s.nodes[i] != nil && !s.flushed {
		s.dirty[i] = true
	}
}

func (s *sim) electionTick() int {
	if s.strict {
		return 8
	}
	return 1 << 30
}

func (s *sim) leader() int {
	for i, n := range s.nodes {
		if n != nil && n.Status().RaftState == raft.StateLeader {
			return i
		}
	}
	return -1
}

func (s *sim) up() []int {
	var up []int
	for i, n := range s.nodes {
		if n != nil {
			up = append(up, i)
		}
	}
	return up
}

// work is one step of a node's queued work with AsyncStorageWrites: its
// next write is made, the messages that waited for a write leave, its next
// committed entries are applied, or raft is told they are. It returns false
// if no node has any.
func (s *sim) work() bool {
	r := s.rng
	type job struct {
		i    int
		kind int
	}
	var jobs []job
	for _, i := range s.up() {
		w, a := s.nodes[i].Pending()
		if s.stall[i] > 0 {
			w = 0 // a slow disk: neither a write nor what waits for one
		} else if s.wip[i] != nil {
			jobs = append(jobs, job{i, 1})
		} else if w > 0 {
			jobs = append(jobs, job{i, 0})
		}
		if s.aip[i] != nil {
			jobs = append(jobs, job{i, 3})
		} else if a > 0 {
			jobs = append(jobs, job{i, 2})
		}
	}
	if len(jobs) == 0 {
		return false
	}
	j := jobs[r.IntN(len(jobs))]
	i := j.i
	n := s.nodes[i]
	switch j.kind {
	case 0:
		s.guard(i, func() {
			w := n.NextWrite()
			n.RunWrite(w)
			s.wip[i] = w
			if w.Restores() && s.snaps && r.IntN(2) == 0 {
				// The service takes a snapshot of its own just after a
				// leader's has been written, before the node takes note.
				_ = n.Snapshot(n.Applied(), nil)
				return
			}
			if r.IntN(3) != 0 { // usually the messages leave at once
				s.wip[i] = nil
				n.DoneWrite(w)
			}
		})
	case 1:
		s.guard(i, func() {
			w := s.wip[i]
			s.wip[i] = nil
			n.DoneWrite(w)
		})
	case 2:
		s.guard(i, func() {
			a := n.NextApply()
			n.RunApply(a)
			s.aip[i] = a
			if r.IntN(3) != 0 {
				s.aip[i] = nil
				n.DoneApply(a)
			}
		})
	case 3:
		s.guard(i, func() {
			a := s.aip[i]
			s.aip[i] = nil
			n.DoneApply(a)
		})
	}
	return true
}

// snapStatusOf tells the sender of a snapshot how it fared, if the program
// is to (-snapstatus).
func (s *sim) snapStatusOf(m *pb.Message, ok bool) {
	if !s.snapStatus || m.GetType() != pb.MsgSnap {
		return
	}
	if i := int(m.GetFrom() - 1); s.nodes[i] != nil {
		s.guard(i, func() { s.nodes[i].SnapshotStatus(m.GetTo(), ok) })
	}
}

// change is a change of membership to ask node i for, made with an eye on
// the configuration that node has now, so that most changes change
// something: usually one voter or learner added or removed, sometimes
// several at once, sometimes leaving a joint configuration.
func (s *sim) change(i int) pb.ConfChangeI {
	r := s.rng
	cs := s.nodes[i].Conf()
	voter := map[uint64]bool{}
	for _, id := range cs.GetVoters() {
		voter[id] = true
	}
	if len(cs.GetVotersOutgoing()) > 0 && r.IntN(2) == 0 || r.IntN(12) == 0 {
		return &pb.ConfChangeV2{} // leave the joint configuration
	}
	used := map[uint64]bool{}
	one := func() *pb.ConfChangeSingle {
		id := uint64(1 + r.IntN(s.n))
		for used[id] {
			id = uint64(1 + r.IntN(s.n))
		}
		used[id] = true
		t := pb.ConfChangeAddNode
		switch k := r.IntN(10); {
		case id == s.anchor:
		case voter[id] && k < 7:
			t = pb.ConfChangeRemoveNode
		case voter[id] && k < 8, !voter[id] && k < 2:
			t = pb.ConfChangeAddLearnerNode
		case !voter[id] && k < 3:
			t = pb.ConfChangeRemoveNode
		}
		return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)}
	}
	switch k := r.IntN(10); {
	case k < 2: // the older form of a change of one node
		c := one()
		return &pb.ConfChange{Type: c.Type, NodeId: c.NodeId}
	case k < 6:
		return &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{one()}}
	}
	// A joint change, of one node or more, left by raft or by a later change.
	c := &pb.ConfChangeV2{}
	for range 1 + r.IntN(3) {
		c.Changes = append(c.Changes, one())
	}
	tr := []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto, pb.ConfChangeTransitionJointImplicit, pb.ConfChangeTransitionJointExplicit}[r.IntN(3)]
	c.Transition = tr.Enum()
	return c
}

func (s *sim) step() {
	r := s.rng
	for _, i := range s.up() {
		if s.snapDue[i] {
			s.guard(i, func() {
				if at := s.nodes[i].Applied(); s.nodes[i].Snapshot(at, nil) == nil {
					s.snapAt[i] = at
					s.snapDue[i] = false
				}
			})
		}
	}
	up := s.up()
	pick := func() int { return up[r.IntN(len(up))] }
	if s.batch {
		if !s.async {
			// Now and then a node is busy with a write for a while, and
			// its input piles up.
			for i := range s.stall {
				if s.stall[i] > 0 {
					s.stall[i]--
				}
			}
			if r.IntN(60) == 0 {
				s.stall[r.IntN(s.n)] = 10 + r.IntN(80)
			}
		}
		// A node that has been given input takes its Ready now, or is
		// given more first.
		for _, i := range up {
			if s.dirty[i] && (s.async || s.stall[i] == 0) && r.IntN(s.flushOdds) == 0 {
				s.dirty[i] = false
				s.flushed = true
				s.guard(i, func() { s.nodes[i].Flush() })
				s.flushed = false
			}
		}
		up = s.up()
		if len(up) == 0 {
			up = nil
		}
	}
	if s.async {
		for i := range s.stall {
			if s.stall[i] > 0 {
				s.stall[i]--
			}
		}
		// Now and then a node's disk is slow for a while, so that its writes
		// are overtaken by what the node does next.
		if r.IntN(60) == 0 {
			s.stall[r.IntN(s.n)] = 10 + r.IntN(80)
		}
		if r.IntN(100) < 45 && s.work() {
			return
		}
	}
	switch c := r.IntN(1000); {
	case c < 600 && len(s.net) > 0: // deliver a message
		// Mostly the oldest that can be delivered, sometimes any: reordering.
		var ok []int
		for k, m := range s.net {
			if !s.cut[m.GetTo()-1] && !s.cut[m.GetFrom()-1] {
				ok = append(ok, k)
			}
		}
		if len(ok) == 0 {
			return
		}
		k := ok[0]
		if r.IntN(4) == 0 {
			k = ok[r.IntN(len(ok))]
		}
		m := s.net[k]
		if r.IntN(20) != 0 { // else it stays, and is delivered again
			s.net = append(s.net[:k], s.net[k+1:]...)
		}
		if i := int(m.GetTo() - 1); s.nodes[i] != nil {
			s.guard(i, func() { s.nodes[i].Step(proto.Clone(m).(*pb.Message)) })
			s.snapStatusOf(m, true)
		} else {
			s.snapStatusOf(m, false)
		}
	case c < 630 && len(s.net) > 0: // lose a message
		k := r.IntN(len(s.net))
		s.snapStatusOf(s.net[k], false)
		s.net = append(s.net[:k], s.net[k+1:]...)
	case c < 780 && len(up) > 0: // a tick: a leader sends heartbeats
		i := pick()
		if l := s.leader(); l >= 0 && r.IntN(3) != 0 && !s.strict {
			i = l
		}
		s.guard(i, func() { s.nodes[i].Tick() })
	case c < 800 && len(up) > 0 && s.snaps: // a node puts a snapshot in place of the log it has applied
		i := pick()
		// Rather a node with a write made and not yet taken note of: the
		// moment at which a snapshot of its own could follow a leader's
		// to the disk.
		// Elsewhere every second node waits for some entries first, as
		// a service does, so that at that moment it has entries to put
		// away; the others take one whenever asked, so that leaders
		// often have to send one.
		at := s.nodes[i].Applied()
		late := false
		for _, j := range up {
			if s.wip[j] != nil {
				i, late = j, true
				at = s.nodes[j].Applied()
			}
		}
		if late || i%2 == 0 || at >= s.snapAt[i]+uint64(r.IntN(12)) {
			s.guard(i, func() {
				if s.nodes[i].Snapshot(at, nil) == nil {
					s.snapAt[i] = at
				}
			})
		}
	case c < 820 && len(up) > 0 && s.reads: // a read index is asked, usually of the leader
		i := pick()
		if l := s.leader(); l >= 0 && r.IntN(3) != 0 {
			i = l
		}
		s.readCtx++
		ctx := []byte(fmt.Sprintf("%08d", s.readCtx))
		s.guard(i, func() { s.nodes[i].ReadIndex(ctx) })
	case s.member && c >= 850 && c < 900 && len(up) > 0: // a change of membership, usually asked of the leader
		i := pick()
		if l := s.leader(); l >= 0 && r.IntN(8) != 0 {
			i = l
		}
		cc := s.change(i)
		s.guard(i, func() { _ = s.nodes[i].ProposeConfChange(cc) })
	case c < 900 && len(up) > 0: // a proposal, usually to the leader
		i := pick()
		if l := s.leader(); l >= 0 && r.IntN(8) != 0 {
			i = l
		}
		s.value++
		v := []byte(fmt.Sprintf("v%d", s.value))
		s.guard(i, func() { _ = s.nodes[i].Propose(v) })
	case s.transfer && c < 912 && len(up) > 0: // a node is asked to hand leadership to another, usually the leader
		i := pick()
		if l := s.leader(); l >= 0 && r.IntN(6) != 0 {
			i = l
		}
		to := uint64(1 + r.IntN(s.n))
		s.guard(i, func() { s.nodes[i].TransferLeader(to) })
	case c < 930 && len(up) > 0: // an election, more often when there is no leader
		if s.leader() >= 0 && r.IntN(4) != 0 {
			return
		}
		i := pick()
		s.guard(i, func() { s.nodes[i].Campaign() })
	case c < 950 && len(up) > 0: // kill a node: now, or at one of its next reports
		if r.IntN(s.calm) != 0 {
			return
		}
		i := pick()
		if r.IntN(3) == 0 {
			s.nodes[i] = nil
			s.fuse[i] = 0
			s.wip[i], s.aip[i] = nil, nil
		} else {
			// A batching node makes about three reports where another makes
			// one.
			span := 6
			if s.batch {
				span = 18
			}
			s.fuse[i] = 1 + r.IntN(span)
		}
	case c < 985: // start a node that is down
		for i := range s.nodes {
			if s.nodes[i] == nil && r.IntN(2) == 0 {
				s.start(i)
				return
			}
		}
	default: // cut a node off, or reconnect one
		i := r.IntN(s.n)
		s.cut[i] = !s.cut[i] && r.IntN(3) != 0 && r.IntN(s.calm) == 0
	}
}

func main() {
	seed := flag.Uint64("seed", 1, "seed")
	n := flag.Int("nodes", 3, "number of nodes")
	steps := flag.Int("steps", 2000, "simulator steps")
	out := flag.String("out", "stream.ndjson", "stream file")
	verbose := flag.Bool("v", false, "print raft's log")
	size := flag.Int64("size", -1, "MaxSizePerMsg; by default 0, 64 or unlimited, chosen by the seed")
	strict := flag.Bool("prevote", false, "PreVote and CheckQuorum on; elections by raft's own timeouts")
	cq := flag.Bool("checkquorum", false, "CheckQuorum on, PreVote off; elections by raft's own timeouts")
	transfer := flag.Bool("transfer", false, "nodes are asked to hand leadership over")
	forward := flag.Bool("forward", false, "a follower passes a proposal on to its leader")
	snapStatus := flag.Bool("snapstatus", false, "with -snap: a leader is told whether each snapshot it sent arrived or was lost")
	inflight := flag.Int("inflight", 0, "MaxInflightMsgs (0: 256)")
	batch := flag.Bool("batch", false, "a node takes one Ready, and makes one write, for several inputs")
	split := flag.String("split", "", "make a Ready's state several writes: term-entries-commit, hardstate-entries, entries-hardstate")
	boot := flag.Bool("boot", true, "every log starts with one entry at term 1")
	async := flag.Bool("async", false, "AsyncStorageWrites")
	nohold := flag.Bool("nohold", false, "with -async: a request for votes does not wait for its write (raft as it is upstream: FIXES.md, E1)")
	parallel := flag.Bool("parallel", false, "a leader sends its requests before it writes")
	reads := flag.Bool("reads", false, "ask nodes for read indexes (raft's ReadIndex)")
	snaps := flag.Bool("snap", false, "nodes take snapshots of what they have applied, and leaders send them")
	member := flag.Bool("member", false, "nodes are asked to change the membership")
	voters := flag.Int("voters", 0, "how many nodes, the first ones, are voters at the start (0: all)")
	calm := flag.Int("calm", 1, "kills and cuts are this many times rarer")
	stepDown := flag.Bool("stepdown", false, "a leader that applies its own removal stops leading (StepDownOnRemoval)")
	flag.Parse()

	f, err := os.Create(*out)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	s := &sim{
		rng: rand.New(rand.NewPCG(*seed, 0x9e3779b97f4a7c15)), out: json.NewEncoder(f), n: *n,
		nodes: make([]*rawnode.Node, *n), disks: make([]*rawnode.MemDisk, *n), fuse: make([]int, *n), cut: make([]bool, *n),
		applied: map[uint64]string{}, logger: quiet{}, boot: *boot, strict: *strict || *cq, prevote: *strict, checkQuorum: *strict || *cq, split: *split,
		transfer: *transfer, forward: *forward, snapStatus: *snapStatus, inflight: *inflight, batch: *batch, dirty: make([]bool, *n),
		async: *async, nohold: *nohold, parallel: *parallel, reads: *reads, snaps: *snaps, wip: make([]*rawnode.Write, *n), aip: make([]*rawnode.Apply, *n), stall: make([]int, *n), snapAt: make([]uint64, *n), snapDue: make([]bool, *n),
	}
	if *verbose {
		s.logger = nil // raft's default
	}
	s.member, s.voters, s.stepDown, s.calm = *member, *voters, *stepDown, max(*calm, 1)
	if s.voters <= 0 || s.voters > s.n {
		s.voters = s.n
	}
	s.anchor = 1 + (*seed/7)%uint64(s.voters)
	s.maxSize = []uint64{0, 64, 1 << 20}[*seed%3]
	s.flushOdds = []int{2, 5, 8}[(*seed/3)%3]
	if *size >= 0 {
		s.maxSize = uint64(*size)
	}
	for i := range s.disks {
		s.disks[i] = &rawnode.MemDisk{}
		s.start(i)
	}
	for k := 0; k < *steps && s.failure == ""; k++ {
		s.step()
	}
	_ = f.Close()
	if s.failure != "" {
		fmt.Println(s.failure)
		os.Exit(3)
	}
	fmt.Printf("ended: %d events\n", s.k)
}

// quiet is a raft.Logger that says nothing and panics where raft's does.
type quiet struct{}

func (quiet) Debug(...any)              {}
func (quiet) Debugf(string, ...any)     {}
func (quiet) Error(...any)              {}
func (quiet) Errorf(string, ...any)     {}
func (quiet) Info(...any)               {}
func (quiet) Infof(string, ...any)      {}
func (quiet) Warning(...any)            {}
func (quiet) Warningf(string, ...any)   {}
func (quiet) Fatal(v ...any)            { panic(fmt.Sprint(v...)) }
func (quiet) Fatalf(f string, v ...any) { panic(fmt.Sprintf(f, v...)) }
func (quiet) Panic(v ...any)            { panic(fmt.Sprint(v...)) }
func (quiet) Panicf(f string, v ...any) { panic(fmt.Sprintf(f, v...)) }
