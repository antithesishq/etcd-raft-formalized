# Faults in etcd-io/raft, patches and workarounds

Raft's source in this checkout is upstream's. A patch is applied only when asked
(`PATCH=E1` or `PATCH=E3` for the local, simulator and Antithesis scripts; [`../scripts/e1.sh`](../scripts/e1.sh) and
[`../scripts/e3.sh`](../scripts/e3.sh) apply them to a copy). Raft's own tests pass with E3; with E1 all pass but
two golden files of `TestInteraction` ([`testdata/async_storage_writes*.txt`](../../testdata/)), whose expected
output has the vote request leave before the write.

| | Fault | Breaks | Fix | Reproducer | Upstream |
|---|---|---|---|---|---|
| E1 | With `AsyncStorageWrites`, a `MsgVote` is sent before the candidate's new term and last entries are on disk | State machine safety | [`E1-vote-request-after-write.patch`](E1-vote-request-after-write.patch), or the application holds vote requests until their write (`rawnode` does, by default) | [`repro/asyncvote`](../repro/asyncvote/), [`../scripts/e1.sh`](../scripts/e1.sh) | [etcd-io/raft#551](https://github.com/etcd-io/raft/issues/551); same fix proposed in [#550](https://github.com/etcd-io/raft/pull/550) |
| E2 | `Config{MaxSizePerMsg: 0}` (documented as "at most one entry per message") with `MaxCommittedSizePerReady` unset | Panic at the first apply | Set `MaxCommittedSizePerReady` (`rawnode` does) | the simulator, any seed choosing size 0 | Not reported |
| E3 | With membership changes, a node whose disk keeps an entry but loses the commit index that came with it is elected with a configuration two changes old | State machine safety | [`E3-campaign-with-one-unapplied-change.patch`](E3-campaign-with-one-unapplied-change.patch), or write each `Ready` atomically and synced (`rawnode` does) | [`repro/confsplit`](../repro/confsplit/), [`../scripts/e3.sh`](../scripts/e3.sh) | [etcd-io/raft#558](https://github.com/etcd-io/raft/issues/558) |
| E4 | An empty `ConfChangeV2` with `Transition` other than `Auto`, proposed in a joint configuration | Panic on apply, on every node and at every restart | Do not propose one (the driver and simulator do not) | `go run ./repro/emptyjoint` | Not reported |

Without `AsyncStorageWrites`, or with it and vote requests held until their write, on
storage that writes each `Ready` atomically, the harness has found no other fault.

## E1. With `AsyncStorageWrites`, a vote request leaves before it is true on disk

`raft.send` makes `MsgAppResp`, `MsgVoteResp` and `MsgPreVoteResp` wait for the write of the
`Ready` they come in, but not `MsgVote`. The request names the candidate's new term and last
entry, neither of which need be durable yet. A candidate that crashes before the write comes
back in its earlier term without those entries, can start an election for the same term
again, and votes granted to its first request (for the longer log) still count.

Schedule ([`repro/asyncvote`](../repro/asyncvote/), three nodes): node 1 leads term 1 and commits an entry at index
2 with node 2. Node 3 has received the entry but not written it, starts an election for term
2 describing a log ending at index 2, and node 2 grants. Node 3 crashes before any write,
restarts with a log ending at index 1, starts term 2 again, votes for itself, and receives the
delayed grant: it leads term 2 without the committed entry, overwrites index 2 on node 2, and
commits. Nodes 1 and 3 apply different entries at index 2. Every step follows the documented
contract of `AsyncStorageWrites`.

The patch adds `MsgVote` to the messages that wait. Without `AsyncStorageWrites` nothing
changes (the application writes before sending, per [`doc.go`](../../doc.go)). In the model a request for
votes is made from the candidate's disk (`StartElection`); unpatched raft in this mode is
rejected by the trace check at its first vote request.

## E3. A commit index lost between two membership changes elects a stale configuration

Raft switches configuration when the application applies a change, not when it is appended.
Two checks keep that safe: a leader appends a change only after applying every earlier one
(`pendingConfIndex`), and a node does not campaign while a committed change is unapplied
(`hasUnappliedConfChanges`). The second asks the node's commit index. Every request that
carries a second change also carries a commit index covering the first, so normally all but
the last change in a log are known to be committed.

Raft's README allows writing a `Ready`'s entries before its HardState on storage without
atomic writes; `MustSync` also lets a HardState that only moves the commit index go unsynced.
A node that crashes between the two writes keeps the second change but not the commit index
covering the first, restarts with the configuration from before both, campaigns, and can win
with voters who do not overlap the current configuration's quorum.

Schedule ([`repro/confsplit`](../repro/confsplit/), five nodes, voters 1–3): node 1 leads term 2, commits the change
adding node 4 (index 3) with node 3, then appends the change adding node 5 (index 4). Node 2
writes that entry and crashes before writing the HardState with commit index 3. Nodes 1, 3, 4
commit index 4, and nodes 1, 4, 5 commit an entry at index 5. Node 2 restarts with commit
index 2 and voters {1, 2, 3}, is elected by itself and node 3, and commits its own entry at
index 5. The same happens with one joint change with automatic leave, which is also two
entries. With one atomic write, or with the patch, nobody is wrongly elected.

The patch scans to the end of the log and refuses to campaign when two or more changes are
unapplied (all but the last are committed whatever the commit index says), or one is
committed by the commit index. With `DisableConfChangeValidation` it keeps upstream
behaviour. Cost: such a node waits for a leader to tell it the commit index.

In the model, `BecomeLeader` requires at most one change not yet switched to
(`OneWaiting`); the trace check rejects a run where a node becomes leader with two.

## E4. An empty `ConfChangeV2` with a `Transition` set panics every node

`stepLeader` treats any change with no `Changes` as leaving a joint configuration
(`len(cc.AsV2().Changes) == 0`) and appends it. `applyConfChange` asks
`ConfChangeV2.LeaveJoint`, which also requires `Transition == Auto`; otherwise the change is
read as entering a joint configuration, `Changer.EnterJoint` returns "config is already
joint", and raft panics. The entry is committed, so every node panics on applying it and at
every restart. The model's `Legal` follows the apply side, and the trace check rejects the
leader's append.

## Workarounds and notes for applications

How the harness ([`../rawnode/`](../rawnode/), [`../server/`](../server/)) uses raft so that it stays within the model and
does not fail. None is a fault in raft; each is a requirement not stated where an
application writer would look.

| | Requirement | What the harness does |
|---|---|---|
| N1 | With `AsyncStorageWrites`, a snapshot must not be beyond the durable commit index: otherwise, after a crash, `loadState` panics ("state.commit N is out of range") | Takes a snapshot only up to the commit index on disk (`Node.Snapshot`) |
| N2 | Raft modifies messages it is handed: a follower forwards `MsgReadIndex` by setting `To` in the caller's message | Records the address before calling `Step` |
| N3 | With `AsyncStorageWrites`, the application's own snapshot must not be written after a pending snapshot from the leader: the node is left with an older snapshot and a gap in its log | Takes no snapshot while a leader's snapshot is pending; storage refuses a snapshot older than the one it holds |
| N4 | [`doc.go`](../../doc.go) says messages "may be sent while entries from the same batch are being persisted"; `Ready.Messages` in [`node.go`](../../node.go) says a follower's responses must wait. The latter is right | Sends after the write (sending before is one of the seeded bugs, and is rejected) |
| N5 | A node added after a leader took a snapshot refuses that snapshot (not in its `ConfState`), and makes no progress until a newer one exists | Takes a snapshot right after applying each membership change (`Config.Changed`) |
| N6 | Without `StepDownOnRemoval`, a leader that removes itself keeps leading and drops all proposals | Transfers leadership to a voter when leading without being one (`handOver`); `STEP_DOWN=1` sets the option |
| N7 | Raft takes a leader snapshot's configuration when handed it; calling `ApplyConfChange` afterwards for an entry at or below the snapshot applies it twice | Reports no change at or below the last snapshot raft was handed |
| N8 | Raft's README order for non-atomic storage (entries, then HardState) can leave entries of a term the node has not recorded; that state is outside the model and unproved ([`../spec/README.md`](../spec/README.md), write order) | Writes each `Ready` atomically; alternatively term and vote, then entries, then commit index is covered by the proofs |
