// emptyjoint shows patches/README.md, E4, on one raft node (a RawNode on raft's own
// MemoryStorage): a ConfChangeV2 with no changes and a Transition other
// than Auto.
//
// Raft's check when the change is proposed (stepLeader) takes any change
// with no changes for the one that leaves a joint configuration, and in a
// joint configuration lets it through. When it is applied
// (ConfChangeV2.LeaveJoint, EnterJoint) it leaves only if its Transition is
// Auto too; otherwise it is a joint change, which a joint configuration
// cannot take, and ApplyConfChange panics with "config is already joint".
// The entry is committed, so every node that applies it panics, and again
// when it starts again.
//
//	go run ./repro/emptyjoint
//
// Exit status: 3 if raft panicked, 0 if it did not.
package main

import (
	"fmt"
	"io"
	"log"
	"os"

	"google.golang.org/protobuf/proto"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// run takes raft's Ready until there is none: writes, and applies what is
// committed, telling raft of each change of membership. It returns the
// types of the entries applied.
func run(rn *raft.RawNode, st *raft.MemoryStorage) (applied []pb.EntryType) {
	for rn.HasReady() {
		rd := rn.Ready()
		if !raft.IsEmptyHardState(rd.HardState) {
			_ = st.SetHardState(rd.HardState)
		}
		_ = st.Append(rd.Entries)
		for _, e := range rd.CommittedEntries {
			applied = append(applied, e.GetType())
			if e.GetType() == pb.EntryConfChangeV2 {
				cc := &pb.ConfChangeV2{}
				if err := proto.Unmarshal(e.GetData(), cc); err != nil {
					panic(err)
				}
				cs := rn.ApplyConfChange(cc)
				fmt.Printf("applied the change at index %d: voters %v, before them %v\n", e.GetIndex(), cs.GetVoters(), cs.GetVotersOutgoing())
			}
		}
		rn.Advance(rd)
	}
	return applied
}

func main() {
	st := raft.NewMemoryStorage()
	_ = st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index: new(uint64(1)), Term: new(uint64(1)), ConfState: &pb.ConfState{Voters: []uint64{1}}}})
	rn, err := raft.NewRawNode(&raft.Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 16, Logger: &raft.DefaultLogger{Logger: log.New(io.Discard, "", 0)}})
	if err != nil {
		panic(err)
	}
	_ = rn.Campaign()
	run(rn, st)

	// A joint change that stays until it is left: node 2 becomes a learner.
	explicit := pb.ConfChangeTransitionJointExplicit.Enum()
	_ = rn.ProposeConfChange(&pb.ConfChangeV2{Transition: explicit,
		Changes: []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(2))}}})
	run(rn, st)

	// No changes, and the same Transition.
	fmt.Println("proposing a ConfChangeV2 with no changes and Transition JointExplicit")
	_ = rn.ProposeConfChange(&pb.ConfChangeV2{Transition: explicit})
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("PANIC when the change is applied: %v\n", r)
			os.Exit(3)
		}
	}()
	types := run(rn, st)
	fmt.Printf("no panic; applied entries of types %v\n", types)
}
