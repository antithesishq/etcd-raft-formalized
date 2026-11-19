package rawnode

import (
	"encoding/binary"
	"errors"

	bolt "go.etcd.io/bbolt"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// Disk is a node's durable state: the HardState, the log, and a snapshot of
// the state machine that stands for the log up to its index. A Save or a
// SaveSnapshot is one atomic write. After a kill, either all of it happened
// or none.
type Disk interface {
	// Load returns what was last saved: a zero HardState, no snapshot (nil)
	// and no entries for a node that has saved nothing. The entries start
	// right after the snapshot's index.
	Load() (*pb.HardState, *pb.Snapshot, []*pb.Entry, error)
	// Save writes hs if it is not nil, and, if there are entries, removes
	// every entry from the first one's index on and appends them.
	Save(hs *pb.HardState, ents []*pb.Entry) error
	// SaveSnapshot stores the snapshot, with hs if it is not nil. With
	// restore, the log is replaced by the snapshot (every entry goes);
	// without, the entries after the snapshot's index stay.
	SaveSnapshot(snap *pb.Snapshot, hs *pb.HardState, restore bool) error
}

// BoltDisk keeps the HardState and the log in one bbolt file. A Save is one
// transaction.
type BoltDisk struct{ db *bolt.DB }

var (
	bucketMeta = []byte("meta")
	bucketLog  = []byte("log")
	keyHard    = []byte("hardstate")
	keySnap    = []byte("snapshot")
)

func OpenBolt(path string) (*BoltDisk, error) {
	db, err := bolt.Open(path, 0o600, nil)
	if err != nil {
		return nil, err
	}
	err = db.Update(func(tx *bolt.Tx) error {
		if _, err := tx.CreateBucketIfNotExists(bucketMeta); err != nil {
			return err
		}
		_, err := tx.CreateBucketIfNotExists(bucketLog)
		return err
	})
	if err != nil {
		return nil, err
	}
	return &BoltDisk{db: db}, nil
}

func (d *BoltDisk) Close() error { return d.db.Close() }

func indexKey(i uint64) []byte {
	k := make([]byte, 8)
	binary.BigEndian.PutUint64(k, i)
	return k
}

func (d *BoltDisk) Load() (*pb.HardState, *pb.Snapshot, []*pb.Entry, error) {
	hs := &pb.HardState{}
	var snap *pb.Snapshot
	var ents []*pb.Entry
	err := d.db.View(func(tx *bolt.Tx) error {
		if b := tx.Bucket(bucketMeta).Get(keyHard); b != nil {
			if err := proto.Unmarshal(b, hs); err != nil {
				return err
			}
		}
		if b := tx.Bucket(bucketMeta).Get(keySnap); b != nil {
			snap = &pb.Snapshot{}
			if err := proto.Unmarshal(b, snap); err != nil {
				return err
			}
		}
		base := snap.GetMetadata().GetIndex()
		return tx.Bucket(bucketLog).ForEach(func(k, v []byte) error {
			e := &pb.Entry{}
			if err := proto.Unmarshal(v, e); err != nil {
				return err
			}
			if e.GetIndex() != base+uint64(len(ents))+1 || binary.BigEndian.Uint64(k) != e.GetIndex() {
				return errors.New("kit: the stored log has a hole")
			}
			ents = append(ents, e)
			return nil
		})
	})
	return hs, snap, ents, err
}

func (d *BoltDisk) SaveSnapshot(snap *pb.Snapshot, hs *pb.HardState, restore bool) error {
	return d.db.Update(func(tx *bolt.Tx) error {
		// A snapshot the node took never replaces a later one.
		if b := tx.Bucket(bucketMeta).Get(keySnap); b != nil && !restore {
			old := &pb.Snapshot{}
			if err := proto.Unmarshal(b, old); err != nil {
				return err
			}
			if old.GetMetadata().GetIndex() >= snap.GetMetadata().GetIndex() {
				return errors.New("kit: a snapshot older than the one on disk")
			}
		}
		b, err := proto.Marshal(snap)
		if err != nil {
			return err
		}
		if err := tx.Bucket(bucketMeta).Put(keySnap, b); err != nil {
			return err
		}
		if hs != nil {
			b, err := proto.Marshal(hs)
			if err != nil {
				return err
			}
			if err := tx.Bucket(bucketMeta).Put(keyHard, b); err != nil {
				return err
			}
		}
		c := tx.Bucket(bucketLog).Cursor()
		for k, _ := c.First(); k != nil; k, _ = c.Next() {
			if !restore && binary.BigEndian.Uint64(k) > snap.GetMetadata().GetIndex() {
				break
			}
			if err := c.Delete(); err != nil {
				return err
			}
		}
		return nil
	})
}

func (d *BoltDisk) Save(hs *pb.HardState, ents []*pb.Entry) error {
	return d.db.Update(func(tx *bolt.Tx) error {
		if hs != nil {
			b, err := proto.Marshal(hs)
			if err != nil {
				return err
			}
			if err := tx.Bucket(bucketMeta).Put(keyHard, b); err != nil {
				return err
			}
		}
		if len(ents) == 0 {
			return nil
		}
		lg := tx.Bucket(bucketLog)
		c := lg.Cursor()
		for k, _ := c.Seek(indexKey(ents[0].GetIndex())); k != nil; k, _ = c.Next() {
			if err := c.Delete(); err != nil {
				return err
			}
		}
		for _, e := range ents {
			b, err := proto.Marshal(e)
			if err != nil {
				return err
			}
			if err := lg.Put(indexKey(e.GetIndex()), b); err != nil {
				return err
			}
		}
		return nil
	})
}

// MemDisk is a Disk in memory, for the simulator. It survives the Node
// that uses it, as a file would.
type MemDisk struct {
	hs   *pb.HardState
	snap *pb.Snapshot
	ents []*pb.Entry // after the snapshot's index
}

func (d *MemDisk) Load() (*pb.HardState, *pb.Snapshot, []*pb.Entry, error) {
	hs := &pb.HardState{}
	if d.hs != nil {
		hs = proto.Clone(d.hs).(*pb.HardState)
	}
	return hs, d.snap, append([]*pb.Entry(nil), d.ents...), nil
}

func (d *MemDisk) Save(hs *pb.HardState, ents []*pb.Entry) error {
	if hs != nil {
		d.hs = proto.Clone(hs).(*pb.HardState)
	}
	if len(ents) > 0 {
		at := ents[0].GetIndex() - d.snap.GetMetadata().GetIndex() - 1
		d.ents = append(d.ents[:at:at], ents...)
	}
	return nil
}

func (d *MemDisk) SaveSnapshot(snap *pb.Snapshot, hs *pb.HardState, restore bool) error {
	if !restore && d.snap.GetMetadata().GetIndex() >= snap.GetMetadata().GetIndex() {
		return errors.New("kit: a snapshot older than the one on disk")
	}
	if hs != nil {
		d.hs = proto.Clone(hs).(*pb.HardState)
	}
	if restore {
		d.ents = nil
	} else {
		d.ents = append([]*pb.Entry(nil), d.ents[snap.GetMetadata().GetIndex()-d.snap.GetMetadata().GetIndex():]...)
	}
	d.snap = snap
	return nil
}

// store is what raft reads its stable log from (raft.Storage): a copy in
// memory of what is on the Disk. The configuration raft starts with is the
// one the snapshot holds, or, without a snapshot, the first one.
type store struct {
	hs    *pb.HardState
	first *pb.ConfState // the voters every node starts with
	snap  *pb.Snapshot  // nil: none
	ents  []*pb.Entry   // ents[i] has index base()+i+1
}

// conf is the configuration as of base().
func (s *store) conf() *pb.ConfState {
	if s.snap != nil {
		return s.snap.GetMetadata().GetConfState()
	}
	return s.first
}

// base is the index the snapshot stands for the log up to; 0 without one.
func (s *store) base() uint64 { return s.snap.GetMetadata().GetIndex() }

func (s *store) last() uint64 { return s.base() + uint64(len(s.ents)) }

func (s *store) lastTerm() uint64 {
	if len(s.ents) > 0 {
		return s.ents[len(s.ents)-1].GetTerm()
	}
	return s.snap.GetMetadata().GetTerm()
}

func (s *store) InitialState() (*pb.HardState, *pb.ConfState, error) {
	return s.hs, s.conf(), nil
}

func (s *store) Entries(lo, hi, maxSize uint64) ([]*pb.Entry, error) {
	if lo <= s.base() {
		return nil, raft.ErrCompacted
	}
	if hi > s.last()+1 {
		return nil, raft.ErrUnavailable
	}
	out := s.ents[lo-s.base()-1 : hi-s.base()-1 : hi-s.base()-1]
	var size uint64
	for i, e := range out {
		size += uint64(proto.Size(e))
		if size > maxSize && i > 0 {
			return out[:i:i], nil
		}
	}
	return out, nil
}

func (s *store) Term(i uint64) (uint64, error) {
	switch {
	case i < s.base():
		return 0, raft.ErrCompacted
	case i == s.base():
		return s.snap.GetMetadata().GetTerm(), nil
	case i > s.last():
		return 0, raft.ErrUnavailable
	}
	return s.ents[i-s.base()-1].GetTerm(), nil
}

func (s *store) LastIndex() (uint64, error)  { return s.last(), nil }
func (s *store) FirstIndex() (uint64, error) { return s.base() + 1, nil }

func (s *store) Snapshot() (*pb.Snapshot, error) {
	if s.snap != nil {
		return s.snap, nil
	}
	return &pb.Snapshot{Metadata: &pb.SnapshotMetadata{ConfState: s.first}}, nil
}

func (s *store) save(hs *pb.HardState, ents []*pb.Entry) {
	if hs != nil {
		s.hs = hs
	}
	if len(ents) > 0 {
		at := ents[0].GetIndex() - s.base() - 1
		s.ents = append(s.ents[:at:at], ents...)
	}
}

// compact puts a snapshot of the state machine at an index of the log in
// place of the log up to there.
func (s *store) compact(snap *pb.Snapshot) {
	s.ents = append([]*pb.Entry(nil), s.ents[snap.GetMetadata().GetIndex()-s.base():]...)
	s.snap = snap
}

// restore replaces the log by a snapshot.
func (s *store) restore(snap *pb.Snapshot) {
	s.ents = nil
	s.snap = snap
}
