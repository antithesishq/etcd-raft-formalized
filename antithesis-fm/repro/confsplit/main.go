// confsplit runs one written schedule of five nodes, three of them voters
// at the start, in which two voters are added one after the other, and
// writes the steps the nodes report as a stream, for the stream check. It
// is the schedule of patches/README.md, E3: what raft's rules for a change of
// membership rest on when a node writes a Ready's entries and its
// HardState.
//
//  1. Node 1 is elected.
//  2. Node 1 appends the change that adds node 4, at index 3. Nodes 2 and 3
//     store it; node 2 is told nothing more. Nodes 1 and 3 commit it and
//     node 1 applies it.
//  3. Node 1 appends the change that adds node 5, at index 4. The request
//     that brings it to node 2 says that index 3 is committed. Node 2
//     writes the entry, and is killed before it writes the commit index
//     (-split entries-hardstate: the order raft's README gives for a
//     storage without atomic writes). With one atomic write (-split "")
//     it is killed after the write.
//  4. Nodes 1, 3 and 4 commit that change; node 1 applies it. Nodes 1, 4
//     and 5, three of the five voters, commit and apply an entry at index 5.
//  5. Node 2 restarts and starts an election, and node 3 votes for it: their
//     logs end with the same entry.
//
// After the split write node 2's commit index on disk is 2, so raft does
// not know that the change at index 3 is committed, does not apply it, and
// lets node 2 start an election with the three voters it started with. Two
// votes of three elect it. It appends its own entry at index 5 and commits
// it with node 3: two state machines hold different entries at index 5.
// After the atomic write node 2 knows index 3 to be committed, applies the
// change before it may start an election, and two votes of four elect
// nobody.
//
//	go run ./repro/confsplit -split entries-hardstate -out stream.ndjson
//
// Exit status: 0 the schedule ended; 3 two nodes applied different entries.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"

	"etcd-raft-formalized/rawnode"
)

const n = 5

type killed struct{}

type cluster struct {
	out   *json.Encoder
	k     int
	split string
	nodes [n + 1]*rawnode.Node
	disks [n + 1]*rawnode.MemDisk
	net   []*pb.Message
	// The node that is killed at its second announced write from now, and
	// how many it has announced.
	trap   uint64
	writes int

	applied map[uint64]string
	failure string
}

func name(id uint64) string {
	if id == 0 {
		return ""
	}
	return fmt.Sprintf("raft%d", id)
}

type reporter struct {
	c  *cluster
	id uint64
}

func (r reporter) Emit(msg string, kv ...any) {
	ev := map[string]any{"e": msg, "node": name(r.id)}
	for i := 0; i+1 < len(kv); i += 2 {
		ev[fmt.Sprint(kv[i])] = kv[i+1]
	}
	r.c.k++
	ev["k"] = r.c.k
	if err := r.c.out.Encode(ev); err != nil {
		panic(err)
	}
}

func (r reporter) Do(fn func() error, msg string, kv ...any) error {
	if r.c.trap == r.id {
		if r.c.writes++; r.c.writes == 2 {
			// Killed before the second write of the Ready: it is neither
			// announced nor made.
			panic(killed{})
		}
	}
	r.Emit(msg, kv...)
	return fn()
}

func (c *cluster) start(id uint64) {
	nd, err := rawnode.Start(rawnode.Config{
		ID: id, Peers: []uint64{1, 2, 3}, Name: name, Disk: c.disks[id], Rep: reporter{c, id},
		Send: func(m *pb.Message) { c.net = append(c.net, proto.Clone(m).(*pb.Message)) },
		Apply: func(e *pb.Entry) {
			got := fmt.Sprintf("%d/%x", e.GetTerm(), e.GetData())
			if was, ok := c.applied[e.GetIndex()]; ok && was != got {
				c.failure = fmt.Sprintf("DIVERGED at index %d: %s applied %s, another node %s", e.GetIndex(), name(id), got, was)
			}
			c.applied[e.GetIndex()] = got
		},
		Boot: true, Split: c.split,
		ElectionTick: 1 << 30, HeartbeatTick: 1, MaxSizePerMsg: 1 << 20, Logger: quiet{},
	})
	if err != nil {
		panic(err)
	}
	c.nodes[id] = nd
}

// settle delivers messages among the nodes in `who`, oldest first, until
// none is left. Messages to or from other nodes stay where they are.
func (c *cluster) settle(ids ...uint64) {
	who := map[uint64]bool{}
	for _, id := range ids {
		who[id] = true
	}
	for {
		did := false
		for k := 0; k < len(c.net); k++ {
			m := c.net[k]
			if who[m.GetTo()] && who[m.GetFrom()] && c.nodes[m.GetTo()] != nil {
				c.net = append(c.net[:k], c.net[k+1:]...)
				c.nodes[m.GetTo()].Step(m)
				did = true
				break
			}
		}
		if !did {
			return
		}
	}
}

// drop loses every message from `from` to `to` that is waiting.
func (c *cluster) drop(from, to uint64) {
	var rest []*pb.Message
	for _, m := range c.net {
		if m.GetFrom() != from || m.GetTo() != to {
			rest = append(rest, m)
		}
	}
	c.net = rest
}

// pass hands node `to` the messages from `from` that are waiting: all of
// them, or only the first request to append.
func (c *cluster) pass(from, to uint64, firstApp bool) {
	var now, rest []*pb.Message
	for _, m := range c.net {
		if m.GetFrom() == from && m.GetTo() == to && !(firstApp && (len(now) > 0 || m.GetType() != pb.MsgApp)) {
			now = append(now, m)
		} else {
			rest = append(rest, m)
		}
	}
	c.net = rest
	for _, m := range now {
		c.nodes[to].Step(m)
	}
}

func add(id uint64) *pb.ConfChangeV2 {
	return &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id)}}}
}

// replace is one joint change that puts nodes 4 and 5 in the place of nodes 2
// and 3, with raft leaving the joint configuration by itself (the
// transition is automatic): the application proposes one change, and raft's
// leader appends the second entry, the one that leaves, when it has applied
// the first.
func replace() *pb.ConfChangeV2 {
	ch := func(t pb.ConfChangeType, id uint64) *pb.ConfChangeSingle {
		return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)}
	}
	return &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{
		ch(pb.ConfChangeAddNode, 4), ch(pb.ConfChangeAddNode, 5),
		ch(pb.ConfChangeRemoveNode, 2), ch(pb.ConfChangeRemoveNode, 3)}}
}

// keepEntries loses the messages from `from` to `to` that carry no entry.
func (c *cluster) keepEntries(from, to uint64) {
	var rest []*pb.Message
	for _, m := range c.net {
		if m.GetFrom() != from || m.GetTo() != to || len(m.GetEntries()) > 0 {
			rest = append(rest, m)
		}
	}
	c.net = rest
}

func main() {
	out := flag.String("out", "stream.ndjson", "stream file")
	joint := flag.Bool("joint", false, "one joint change with an automatic leave (nodes 4 and 5 for 2 and 3) instead of two changes")
	split := flag.String("split", "", `"entries-hardstate": a Ready's entries and its HardState are two writes; "": one`)
	flag.Parse()
	f, err := os.Create(*out)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	defer f.Close()
	c := &cluster{out: json.NewEncoder(f), split: *split, applied: map[uint64]string{}}
	for id := uint64(1); id <= n; id++ {
		c.disks[id] = &rawnode.MemDisk{}
		c.start(id)
	}

	// 1. Node 1 is elected; its first entry of the term (index 2) is
	// everywhere and committed.
	c.nodes[1].Campaign()
	c.settle(1, 2, 3)
	c.nodes[1].Tick()
	c.settle(1, 2, 3)

	// 2. The change that adds node 4, at index 3. Node 2 stores it and
	// acknowledges it, and hears nothing more. Nodes 1 and 3 commit it;
	// node 1 applies it.
	// (-joint: the one joint change, at index 3. When node 1 has applied it
	// raft appends the entry that leaves the joint configuration, at index
	// 4, by itself.)
	if *joint {
		_ = c.nodes[1].ProposeConfChange(replace())
	} else {
		_ = c.nodes[1].ProposeConfChange(add(4))
	}
	c.pass(1, 2, true)
	c.settle(1, 3)
	c.pass(2, 1, false)
	if *joint {
		c.keepEntries(1, 2)
	} else {
		c.drop(1, 2)
	}

	// 3. The change that adds node 5, at index 4. Node 2 is brought it by a
	// request that says index 3 is committed, and is killed: between its
	// two writes, or after its one.
	// (-joint: nothing is proposed; the request with index 4 is waiting.)
	if !*joint {
		_ = c.nodes[1].ProposeConfChange(add(5))
	}
	if c.split != "" {
		c.trap = 2
	}
	func() {
		defer func() {
			if r := recover(); r != nil {
				if _, ok := r.(killed); !ok {
					panic(r)
				}
			}
		}()
		c.pass(1, 2, true)
	}()
	c.trap = 0
	c.nodes[2] = nil
	c.drop(1, 2)
	c.drop(2, 1)

	// 4. Nodes 1, 3 and 4 commit the second change and node 1 applies it;
	// node 5 is brought up to date. Then nodes 1, 4 and 5 commit and apply
	// an entry at index 5, of which node 3 hears nothing.
	c.settle(1, 3, 4)
	c.nodes[1].Tick()
	c.settle(1, 3, 4, 5)
	c.drop(1, 3)
	_ = c.nodes[1].Propose([]byte("e"))
	c.settle(1, 4, 5)
	c.nodes[1].Tick()
	c.settle(1, 4, 5)
	c.drop(1, 3)

	// 5. Node 2 restarts and starts an election; node 3 answers.
	c.start(2)
	c.nodes[2].Campaign()
	c.settle(2, 3)
	c.nodes[2].Tick()
	c.settle(2, 3)
	if c.failure != "" {
		fmt.Println(c.failure)
		os.Exit(3)
	}
	fmt.Printf("ended: %d events; node 2 is %s\n", c.k, c.nodes[2].Status().RaftState)
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
