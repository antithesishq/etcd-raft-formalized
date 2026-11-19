// aba runs one written schedule of five nodes with AsyncStorageWrites and
// writes the steps they report as a stream, for the stream check. It is the
// schedule the comment in raft's rawnode.go (newStorageAppendRespMsg)
// describes: a write that is overtaken, while it is being made, by entries
// of a later term at the same index.
//
//  1. Node 1 is elected and everybody has its first entry.
//  2. Node 1 adds an entry at index 3; only node 2 is sent it. Node 2 starts
//     writing it and the write is slow.
//  3. Node 1 stops. Node 3 is elected by 4 and 5, adds its own entry at
//     index 3, and commits it with them.
//  4. Node 2 is sent node 3's entry, which replaces the one it is writing
//     (in memory), and is told that index 3 is committed.
//  5. Node 2's slow write is done.
//
// Raft compares the term of what was written with what it now has at that
// index, finds they differ, and waits for its next write before it applies
// index 3. scripts/aba.sh runs this against raft as it is (the stream is
// accepted) and against raft without that comparison (seeded bug
// stable-to-ignores-term: node 2 hands its state machine the entry it wrote,
// not the one that is committed, and the stream is rejected there).
//
//	go run ./repro/aba -out stream.ndjson
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

type cluster struct {
	out   *json.Encoder
	k     int
	nodes [n + 1]*rawnode.Node
	net   []*pb.Message
	// A node whose disk is slow: its queued writes wait.
	slow [n + 1]bool
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
	r.Emit(msg, kv...)
	return fn()
}

func (c *cluster) start(id uint64) {
	peers := []uint64{1, 2, 3, 4, 5}
	nd, err := rawnode.Start(rawnode.Config{
		ID: id, Peers: peers, Name: name, Disk: &rawnode.MemDisk{}, Rep: reporter{c, id},
		Send:  func(m *pb.Message) { c.net = append(c.net, proto.Clone(m).(*pb.Message)) },
		Apply: func(*pb.Entry) {},
		Async: true, Boot: true,
		ElectionTick: 1 << 30, HeartbeatTick: 1, MaxSizePerMsg: 1 << 20, Logger: quiet{},
	})
	if err != nil {
		panic(err)
	}
	c.nodes[id] = nd
}

// work makes every queued write and applies every queued batch of the nodes
// in `who` whose disk is not slow. It says whether it did anything.
func (c *cluster) work(who map[uint64]bool) bool {
	did := false
	for id := uint64(1); id <= n; id++ {
		nd := c.nodes[id]
		if nd == nil || !who[id] {
			continue
		}
		if !c.slow[id] {
			if w := nd.NextWrite(); w != nil {
				nd.RunWrite(w)
				nd.DoneWrite(w)
				did = true
			}
		}
		if a := nd.NextApply(); a != nil {
			nd.RunApply(a)
			nd.DoneApply(a)
			did = true
		}
	}
	return did
}

// settle delivers messages among the nodes in `who`, oldest first, and does
// their work, until there is nothing left to do. Messages to or from other
// nodes stay where they are.
func (c *cluster) settle(ids ...uint64) {
	who := map[uint64]bool{}
	for _, id := range ids {
		who[id] = true
	}
	for {
		did := c.work(who)
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

// deliver hands node `to` every message from `from` that is waiting.
func (c *cluster) deliver(from, to uint64) {
	var now, rest []*pb.Message
	for _, m := range c.net {
		if m.GetFrom() == from && m.GetTo() == to {
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

func main() {
	out := flag.String("out", "stream.ndjson", "stream file")
	flag.Parse()
	f, err := os.Create(*out)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	defer f.Close()
	c := &cluster{out: json.NewEncoder(f)}
	for id := uint64(1); id <= n; id++ {
		c.start(id)
	}
	all := []uint64{1, 2, 3, 4, 5}

	// 1. Node 1 is elected; its first entry of the term is everywhere and
	// committed.
	c.nodes[1].Campaign()
	c.settle(all...)
	c.nodes[1].Tick()
	c.settle(all...)

	// 2. Node 1 adds an entry at index 3. Only node 2 is sent it; node 2
	// starts the write and it is slow.
	_ = c.nodes[1].Propose([]byte("a"))
	c.work(map[uint64]bool{1: true})
	c.slow[2] = true
	c.deliver(1, 2)
	w1 := c.nodes[2].NextWrite()
	c.nodes[2].RunWrite(w1)

	// 3. Node 1 stops; what it sent to 3, 4 and 5 is lost. Node 3 is elected
	// by 4 and 5, adds its own entry at index 3 and commits it with them.
	c.nodes[1] = nil
	c.net = nil
	c.nodes[3].Campaign()
	c.settle(3, 4, 5)
	c.nodes[3].Tick()
	c.settle(3, 4, 5)

	// 4. Node 2 is sent what node 3 has for it: the entry of the later term
	// at index 3, and then that index 3 is committed.
	c.nodes[3].Tick()
	c.settle(3, 4, 5)
	c.deliver(3, 2)
	c.work(map[uint64]bool{2: true}) // its disk is slow: only what needs no write
	c.deliver(2, 3)
	c.settle(3, 4, 5)
	c.nodes[3].Tick()
	c.work(map[uint64]bool{3: true})
	c.deliver(3, 2)

	// 5. Node 2's slow write is done. With raft as it is, index 3 is not
	// applied before the next write, of the entry that replaced it.
	c.nodes[2].DoneWrite(w1)
	c.work(map[uint64]bool{2: true})
	c.slow[2] = false
	c.settle(2, 3, 4, 5)
	c.nodes[3].Tick()
	c.settle(2, 3, 4, 5)
	fmt.Printf("ended: %d events\n", c.k)
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
