package main

import (
	"encoding/binary"
	"fmt"
	"sync"

	"github.com/antithesishq/antithesis-sdk-go/assert"
)

// A command is one log entry of the service. An add puts Value into the
// running sum; Op is a unique id the client picked, so every applied entry
// can be attributed to exactly one request. A read changes nothing: it
// marks a point in the log, and Op is a number its node picked.
type command struct {
	Kind  byte // 'A' add, 'R' read
	Op    uint64
	Value int64
}

const commandLen = 17

func encodeCommand(c command) []byte {
	b := make([]byte, commandLen)
	b[0] = c.Kind
	binary.BigEndian.PutUint64(b[1:9], c.Op)
	binary.BigEndian.PutUint64(b[9:17], uint64(c.Value))
	return b
}

func decodeCommand(b []byte) (command, error) {
	if len(b) != commandLen || (b[0] != 'A' && b[0] != 'R') {
		return command{}, fmt.Errorf("bad command of length %d", len(b))
	}
	return command{
		Kind:  b[0],
		Op:    binary.BigEndian.Uint64(b[1:9]),
		Value: int64(binary.BigEndian.Uint64(b[9:17])),
	}, nil
}

// fsmState is everything the state machine holds. Index is the log index of
// the last applied add; Digest chains every applied (index, term, op,
// value), so two nodes with the same digest at an index applied the same
// history.
type fsmState struct {
	Index  uint64
	Term   uint64
	Sum    int64
	Count  uint64
	Digest uint64
}

type sumFSM struct {
	node string
	mu   sync.Mutex
	st   fsmState
}

func mix(h, x uint64) uint64 {
	// splitmix64-style mixing, chained.
	h ^= x + 0x9e3779b97f4a7c15 + (h << 6) + (h >> 2)
	h ^= h >> 30
	h *= 0xbf58476d1ce4e5b9
	h ^= h >> 27
	h *= 0x94d049bb133111eb
	h ^= h >> 31
	return h
}

// apply applies one add and returns the state after it.
func (f *sumFSM) apply(index, term uint64, c command) fsmState {
	f.mu.Lock()
	prev := f.st
	assert.Always(index > prev.Index, "a node applies commands in strictly increasing log index order",
		map[string]any{"node": f.node, "index": index, "prev_index": prev.Index})
	assert.Always(term >= prev.Term, "a node applies commands in non-decreasing term order",
		map[string]any{"node": f.node, "index": index, "term": term, "prev_term": prev.Term})
	f.st.Index = index
	f.st.Term = term
	f.st.Sum += c.Value
	f.st.Count++
	f.st.Digest = mix(mix(mix(mix(prev.Digest, index), term), c.Op), uint64(c.Value))
	st := f.st
	f.mu.Unlock()
	logLine("msg=raft-apply index=%d term=%d op=%d value=%d sum=%d count=%d digest=%d",
		st.Index, st.Term, c.Op, c.Value, st.Sum, st.Count, st.Digest)
	return st
}

// restore replaces the state by one a snapshot holds.
func (f *sumFSM) restore(st fsmState) {
	f.mu.Lock()
	f.st = st
	f.mu.Unlock()
	logLine("msg=raft-restore index=%d term=%d sum=%d count=%d digest=%d", st.Index, st.Term, st.Sum, st.Count, st.Digest)
}

func (f *sumFSM) state() fsmState {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.st
}
