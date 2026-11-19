package main

import (
	"bufio"
	"encoding/binary"
	"io"
	"net"
	"time"

	"golang.org/x/sys/unix"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A plain transport: TCP connections to each peer, each message a
// length-prefixed protobuf. A message that cannot be sent is dropped, as
// raft allows; raft is told the peer was unreachable. With more than one
// connection to a peer (the default is two), messages can overtake each
// other, as they can between the stream and pipeline channels of etcd's own
// transport.

const maxFrame = 16 << 20

type peer struct {
	id   uint64
	addr string
	out  chan frame
}

// frame is one message on its way out; snap: it is a snapshot.
type frame struct {
	b    []byte
	snap bool
}

// snapResult says whether a snapshot sent to a peer was written to its
// connection or lost.
type snapResult struct {
	to uint64
	ok bool
}

type transport struct {
	peers       map[uint64]*peer
	in          chan<- *pb.Message
	unreachable chan<- uint64
	snapStatus  chan<- snapResult
}

func newTransport(self uint64, addrs map[uint64]string, conns int, in chan<- *pb.Message, unreachable chan<- uint64, snapStatus chan<- snapResult) *transport {
	t := &transport{peers: map[uint64]*peer{}, in: in, unreachable: unreachable, snapStatus: snapStatus}
	for id, addr := range addrs {
		if id == self {
			continue
		}
		p := &peer{id: id, addr: addr, out: make(chan frame, 256)}
		t.peers[id] = p
		for range conns {
			go t.write(p)
		}
	}
	return t
}

// send queues a message. It is called from raft's goroutine and never
// blocks.
func (t *transport) send(m *pb.Message) {
	p := t.peers[m.GetTo()]
	if p == nil {
		return
	}
	b, err := proto.Marshal(m)
	if err != nil {
		fatal("marshal: %v", err)
	}
	f := frame{b, m.GetType() == pb.MsgSnap}
	select {
	case p.out <- f:
	default:
		// Not on raft's goroutine: the report of a lost snapshot can wait.
		go t.lost(p.id, f)
	}
}

func (t *transport) lost(id uint64, f frame) {
	select {
	case t.unreachable <- id:
	default:
	}
	t.fared(id, f, false)
}

// fared reports how a snapshot fared. The report waits if raft's goroutine
// is busy: raft sends that node no entries until it has it.
func (t *transport) fared(id uint64, f frame, ok bool) {
	if f.snap && t.snapStatus != nil {
		t.snapStatus <- snapResult{id, ok}
	}
}

func (t *transport) write(p *peer) {
	var conn net.Conn
	var w *bufio.Writer
	for f := range p.out {
		b := f.b
		if conn == nil {
			c, err := net.DialTimeout("tcp", p.addr, 500*time.Millisecond)
			if err != nil {
				t.lost(p.id, f)
				continue
			}
			alive(c)
			conn, w = c, bufio.NewWriter(c)
		}
		var hdr [4]byte
		binary.BigEndian.PutUint32(hdr[:], uint32(len(b)))
		_ = conn.SetWriteDeadline(time.Now().Add(time.Second))
		_, err := w.Write(hdr[:])
		if err == nil {
			_, err = w.Write(b)
		}
		if err == nil {
			err = w.Flush()
		}
		if err != nil {
			_ = conn.Close()
			conn = nil
			t.lost(p.id, f)
		} else {
			t.fared(p.id, f, true)
		}
	}
}

// alive makes a connection fail within a few seconds when its peer has
// gone without closing it (a killed container, a cut network). Without
// this, small messages written into such a connection are accepted by the
// kernel for many minutes, and the peer hears nothing from this node until
// the connection is replaced.
func alive(c net.Conn) {
	tc, ok := c.(*net.TCPConn)
	if !ok {
		return
	}
	_ = tc.SetKeepAliveConfig(net.KeepAliveConfig{Enable: true, Idle: time.Second, Interval: time.Second, Count: 2})
	if raw, err := tc.SyscallConn(); err == nil {
		_ = raw.Control(func(fd uintptr) {
			// Data not acknowledged for this long ends the connection.
			_ = unix.SetsockoptInt(int(fd), unix.IPPROTO_TCP, unix.TCP_USER_TIMEOUT, 2500)
		})
	}
}

func (t *transport) listen(bind string) error {
	ln, err := net.Listen("tcp", bind)
	if err != nil {
		return err
	}
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				time.Sleep(10 * time.Millisecond)
				continue
			}
			alive(c)
			go t.read(c)
		}
	}()
	return nil
}

func (t *transport) read(c net.Conn) {
	defer c.Close()
	r := bufio.NewReader(c)
	for {
		var hdr [4]byte
		if _, err := io.ReadFull(r, hdr[:]); err != nil {
			return
		}
		n := binary.BigEndian.Uint32(hdr[:])
		if n > maxFrame {
			return
		}
		b := make([]byte, n)
		if _, err := io.ReadFull(r, b); err != nil {
			return
		}
		m := &pb.Message{}
		if err := proto.Unmarshal(b, m); err != nil {
			return
		}
		t.in <- m
	}
}
