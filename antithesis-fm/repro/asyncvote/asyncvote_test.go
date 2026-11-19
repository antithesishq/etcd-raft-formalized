//go:build e1

// Package asyncvote is one written schedule for etcd-io/raft with
// AsyncStorageWrites, run against the real code: a candidate asks for votes
// before its term and its last entries are on disk, is killed, comes back
// with the shorter log, asks again for the same term and is elected by a
// vote given to the first request. The test fails if two nodes then apply
// different entries at one index, and passes if the schedule cannot be
// followed. See ../../patches/README.md, E1.
package asyncvote

import (
	"testing"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

type cluster struct {
	t     *testing.T
	disk  map[uint64]*raft.MemoryStorage // what is durable
	node  map[uint64]*raft.RawNode
	wr    map[uint64][]*pb.Message // storage writes a node has been handed and not made
	net   []*pb.Message
	apply map[uint64]map[uint64]*pb.Entry // per node: index -> entry applied
}

func (c *cluster) start(id uint64) {
	n, err := raft.NewRawNode(&raft.Config{
		ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: c.disk[id],
		MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, AsyncStorageWrites: true,
	})
	if err != nil {
		c.t.Fatal(err)
	}
	c.node[id], c.wr[id] = n, nil
}

// ready takes everything raft has for the node: messages for other nodes go
// on the network at once, as the async contract allows; writes are queued;
// applies are made.
func (c *cluster) ready(id uint64) {
	n := c.node[id]
	for n.HasReady() {
		rd := n.Ready()
		for _, m := range rd.Messages {
			switch m.GetTo() {
			case raft.LocalAppendThread:
				c.wr[id] = append(c.wr[id], m)
			case raft.LocalApplyThread:
				for _, e := range m.GetEntries() {
					c.apply[id][e.GetIndex()] = e
				}
				for _, r := range m.GetResponses() {
					_ = n.Step(r)
				}
			default:
				c.net = append(c.net, m)
			}
		}
	}
}

// write makes the node's oldest queued write and delivers what waited for it.
func (c *cluster) write(id uint64) {
	m := c.wr[id][0]
	c.wr[id] = c.wr[id][1:]
	if len(m.GetEntries()) > 0 {
		if err := c.disk[id].Append(m.GetEntries()); err != nil {
			c.t.Fatal(err)
		}
	}
	if m.Term != nil || m.Vote != nil || m.Commit != nil {
		_ = c.disk[id].SetHardState(&pb.HardState{Term: m.Term, Vote: m.Vote, Commit: m.Commit})
	}
	for _, r := range m.GetResponses() {
		if r.GetTo() == id {
			_ = c.node[id].Step(r)
		} else {
			c.net = append(c.net, r)
		}
	}
	c.ready(id)
}

func (c *cluster) writeAll(id uint64) {
	for len(c.wr[id]) > 0 {
		c.write(id)
	}
}

// deliver hands the first message of that type between those nodes to its
// receiver and removes it from the network.
func (c *cluster) deliver(ty pb.MessageType, from, to uint64) *pb.Message {
	for k, m := range c.net {
		if m.GetType() == ty && m.GetFrom() == from && m.GetTo() == to {
			c.net = append(c.net[:k], c.net[k+1:]...)
			_ = c.node[to].Step(m)
			c.ready(to)
			return m
		}
	}
	c.t.Fatalf("no %s from %d to %d on the network", ty, from, to)
	return nil
}

func (c *cluster) has(ty pb.MessageType, from, to uint64) bool {
	for _, m := range c.net {
		if m.GetType() == ty && m.GetFrom() == from && m.GetTo() == to {
			return true
		}
	}
	return false
}

func (c *cluster) take(ty pb.MessageType, from, to uint64) *pb.Message {
	for k, m := range c.net {
		if m.GetType() == ty && m.GetFrom() == from && m.GetTo() == to {
			c.net = append(c.net[:k], c.net[k+1:]...)
			return m
		}
	}
	c.t.Fatalf("no %s from %d to %d on the network", ty, from, to)
	return nil
}

func TestCandidateKilledBeforeItsWrite(t *testing.T) {
	c := &cluster{t: t, disk: map[uint64]*raft.MemoryStorage{}, node: map[uint64]*raft.RawNode{},
		wr: map[uint64][]*pb.Message{}, apply: map[uint64]map[uint64]*pb.Entry{}}
	for id := uint64(1); id <= 3; id++ {
		s := raft.NewMemoryStorage()
		// The membership, as a snapshot at index 1, term 1.
		if err := s.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
			Index: new(uint64(1)), Term: new(uint64(1)), ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3}}}}); err != nil {
			t.Fatal(err)
		}
		c.disk[id], c.apply[id] = s, map[uint64]*pb.Entry{}
		c.start(id)
	}

	// 1 is elected in term 2 by 2 and 3, each write made before its reply.
	_ = c.node[1].Campaign()
	c.ready(1)
	c.writeAll(1)
	for _, v := range []uint64{2, 3} {
		c.deliver(pb.MsgVote, 1, v)
		c.writeAll(v)
		c.deliver(pb.MsgVoteResp, v, 1)
	}
	c.writeAll(1)
	if c.node[1].Status().RaftState != raft.StateLeader {
		t.Fatal("1 is not the leader")
	}
	// 1's first entry is index 2. 2 stores it and acknowledges: 1 commits
	// and applies it.
	c.deliver(pb.MsgApp, 1, 2)
	c.writeAll(2)
	c.deliver(pb.MsgAppResp, 2, 1)
	c.writeAll(1)
	committed := c.apply[1][2]
	if committed == nil {
		t.Fatal("1 has not applied index 2")
	}
	t.Logf("1 has applied index 2: term %d", committed.GetTerm())

	// 3 is handed the same entry and does not get to write it.
	c.deliver(pb.MsgApp, 1, 3)
	// 3 starts an election for the next term. Its request goes out at once, and
	// describes a log with the entries it has not written.
	_ = c.node[3].Campaign()
	c.ready(3)
	if !c.has(pb.MsgVote, 3, 2) {
		t.Log("3's request waits for its write: the schedule stops here")
		return
	}
	req := c.deliver(pb.MsgVote, 3, 2)
	t.Logf("3 asks for term %d with last index %d, term %d; on its disk: last index %d",
		req.GetTerm(), req.GetIndex(), req.GetLogTerm(), last(c.disk[3]))
	c.writeAll(2)
	grant := c.take(pb.MsgVoteResp, 2, 3)
	if grant.GetReject() {
		t.Fatal("2 refused")
	}

	// 3 is killed before any of its writes, and starts again from its disk.
	c.start(3)
	t.Logf("3 restarts in term %d with last index %d", c.node[3].Status().GetTerm(), last(c.disk[3]))
	_ = c.node[3].Campaign()
	c.ready(3)
	c.writeAll(3)
	if got := c.node[3].Status().GetTerm(); got != req.GetTerm() {
		t.Skipf("3 is in term %d, not %d again: the schedule does not apply", got, req.GetTerm())
	}
	// The grant 2 gave to the first request arrives.
	_ = c.node[3].Step(grant)
	c.ready(3)
	c.writeAll(3)
	if c.node[3].Status().RaftState != raft.StateLeader {
		t.Skip("3 did not win with the earlier grant: the schedule does not apply")
	}
	t.Logf("3 leads term %d with last index %d", c.node[3].Status().GetTerm(), last(c.disk[3]))

	// 3 replicates its own first entry, also index 2, to 2, which has not
	// heard that index 2 is committed, and commits it.
	c.deliver(pb.MsgApp, 3, 2)
	c.writeAll(2)
	t.Logf("2 now has at index 2 an entry of term %d", termAt(c.disk[2], 2))
	c.deliver(pb.MsgAppResp, 2, 3)
	c.writeAll(3)
	e := c.apply[3][2]
	if e == nil {
		t.Skip("3 did not commit its entry: the schedule does not apply")
	}
	t.Logf("3 has applied index 2: term %d", e.GetTerm())
	if e.GetTerm() != committed.GetTerm() {
		t.Fatalf("two nodes applied different entries at index 2: 1 applied the entry of term %d, 3 the entry of term %d",
			committed.GetTerm(), e.GetTerm())
	}
}

func termAt(s *raft.MemoryStorage, i uint64) uint64 {
	t, _ := s.Term(i)
	return t
}

func last(s *raft.MemoryStorage) uint64 {
	i, _ := s.LastIndex()
	return i
}
