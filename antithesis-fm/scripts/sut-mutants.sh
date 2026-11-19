#!/usr/bin/env bash
# Mutation test of raft: for each mutant (a sed edit of a copy of raft or of
# rawnode, or simulator arguments), build sim/ from the copy, run it on seeds,
# and require some seed to give REJECTED/VIOLATED or a simulator failure
# (panic, divergent applies). The checkout is not changed. Each raft mutant
# is tried as NAME and as NAME+batch (one Ready for several inputs).
#
#   scripts/sut-mutants.sh [NAME]          one mutant, or all
#   SEEDS=200 scripts/sut-mutants.sh       seeds tried for each (default 60)
#   MORE=0 scripts/sut-mutants.sh          no extra seeds (default: up to 4 x SEEDS)
#   LAUNCH=50 scripts/sut-mutants.sh NAME  instead build the cluster with the mutant and launch
#                                          an Antithesis run of that many compute hours; prints
#                                          its id. Rebuild the clean images afterwards.
#   SIMARGS="-size 0" STEPS=8000 scripts/sut-mutants.sh NAME    other simulator settings
#   JOBS=N                                 parallel seeds
#
# Prints per mutant "ok NAME: seed ..." (noting if beyond SEEDS) or FAIL.
# Exit 0 if every mutant was shown.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
seeds=${SEEDS:-60}; steps=${STEPS:-3000}; more=${MORE:-$((seeds * 4))}
only=${1:-}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
fail=0

one() { # sim-binary manifest nodes seed -> prints "seed N: how" if the seed shows the bug
  local sim=$1 manifest=$2 nodes=$3 seed=$4 f="$5/$3-$4.ndjson" out rc v
  out=$("$sim" -seed "$seed" -nodes "$nodes" -steps "$steps" ${SIMARGS:-} ${MUTARGS:-} -out "$f" 2>&1); rc=$?
  touch "$f.eof"
  v=$("$here/tracekit/check/streamcheck.py" "$manifest" "$f" | cut -c1-240)
  rm -f "$f" "$f".*
  case "$v" in ACCEPTED*) [ $rc -eq 0 ] || echo "$seed $nodes nodes: simulator: ${out:0:160}" ;;
               *) echo "$seed $nodes nodes: $v$([ $rc -eq 0 ] || echo "; simulator: ${out:0:120}")" ;; esac
}
export -f one; export here steps SIMARGS

mutant() { # name file sed-expression [simulator arguments]; file "-": no edit, the arguments are the bug
  [ -n "$only" ] && [ "$only" != "$1" ] && return
  local name=$1 file=$2 expr=$3 dir="$work/$1"
  export MUTARGS=${4:-}
  mkdir -p "$dir/src"
  rsync -a --exclude .git --exclude runs --exclude .lake --exclude target --exclude tools "$root/" "$dir/src/"
  if [ "$file" != - ]; then
    sed -i "$expr" "$dir/src/$file"
    if cmp -s "$dir/src/$file" "$root/$file"; then echo "FAIL  $name: the edit did not apply"; fail=1; return; fi
  fi
  if ! ( cd "$dir/src/antithesis-fm" && go build -o "$dir/sim" ./sim ) 2> "$dir/build.log"; then
    echo "FAIL  $name: does not compile: $(head -3 "$dir/build.log" | tr '\n' ' ')"; fail=1; return
  fi
  if [ -n "${LAUNCH:-}" ]; then
    # Antithesis run of the mutant cluster; expected to fail the step-check
    # property or a safety property.
    cp -r "$here/tracekit/tools" "$dir/src/antithesis-fm/tracekit/tools"   # the driver image holds TLC
    ( cd "$dir/src/antithesis-fm/config" && docker compose -f docker-compose.yaml build -q ) > "$dir/build.log" 2>&1 || { echo "FAIL  $name: images do not build: $(tail -2 "$dir/build.log" | tr '\n' ' ' | cut -c1-300)"; fail=1; return; }
    id=$(cd "$dir/src/antithesis-fm" && BUILD=0 VARIANT="$name" REV="$(git -C "$root" rev-parse --short HEAD)" BRANCH="$(git -C "$root" rev-parse --abbrev-ref HEAD)" scripts/launch.sh "$LAUNCH" "etcd-raft formalized, seeded bug: $name" 2>&1 | tee "$here/runs/launch-$name.log" | sed -n 's/.*"runId": "\(.*\)".*/\1/p')
    echo "launched $name: ${id:-NO RUN ID}"
    rm -rf "$dir"
    return
  fi
  local hit="" nodes from lo=1 hi=$seeds late="" sizes="3 5" what="3 and of 5 nodes"
  # Membership changes: five nodes, three voters at the start.
  case "$MUTARGS" in *-member*) sizes=5; what="5 nodes, 3 of them voters at the start" ;; esac
  while [ -z "$hit" ] && [ "$lo" -le "$hi" ]; do
    for nodes in $sizes; do
      manifest="$here/spec/manifest.json"; [ $nodes = 5 ] && manifest="$here/spec/manifest5.json"
      case "$MUTARGS" in *-member*) manifest="$here/spec/manifest-m.json" ;; esac
      for from in $(seq "$lo" 8 "$hi"); do
        hit=$(seq "$from" $((from + 7 < hi ? from + 7 : hi)) | xargs -P "${JOBS:-$(nproc)}" -I{} bash -c "one '$dir/sim' '$manifest' $nodes {} '$dir'" | sort -n | head -1)
        [ -n "$hit" ] && break 2
      done
    done
    [ -z "$hit" ] && [ "$hi" -lt "$more" ] && late=" (not in the first $seeds seeds)"
    lo=$((hi + 1)); hi=$more
  done
  if [ -n "$hit" ]; then echo "ok    $name: seed $hit$late"
  else echo "FAIL  $name: not shown in $((more > seeds ? more : seeds)) seeds of $what"; fail=1; fi
  rm -rf "$dir"
}

# Mutant with one Ready per input, and with -batch.
both() { mutant "$1" "$2" "$3" "${4:-}"; mutant "$1+batch" "$2" "$3" "${4:-} -batch"; }

# A leader commits what the node with the highest index has, not a quorum.
both commit-without-quorum quorum/majority.go \
  's/pos := n - (n\/2 + 1)/pos := n - 1/'
# A leader commits an entry of an earlier term by counting.
both commit-earlier-term log.go \
  's/if at.term != 0 \&\& at.index > l.committed \&\& l.matchTerm(at) {/if at.index > l.committed {/'
# A heartbeat carries the leader's commit index whatever the follower has.
both heartbeat-commit-unbounded raft.go \
  's/commit := min(pr.Match, r.raftLog.committed)/commit := r.raftLog.committed/'
# A node votes again in a term it has voted in.
both votes-twice raft.go \
  's/canVote := r.Vote == m.GetFrom() ||/canVote := true ||/'
# A node votes without comparing logs.
both votes-without-log-check raft.go \
  's/if canVote \&\& r.raftLog.isUpToDate(candLastID) {/if canVote {/'
# A node keeps its vote when it moves to a later term.
both vote-kept-across-terms raft.go \
  '/^func (r \*raft) reset(term uint64) {/,/^}/ s/\t\tr.Vote = None/\t\t_ = None/'
# A follower accepts entries without checking the entry before them.
both no-prev-check log.go \
  's/if !l.matchTerm(a.prev) {/if false \&\& !l.matchTerm(a.prev) {/'
# A request below the commit index is acknowledged at the end of the log.
both ack-committed-at-last-index raft.go \
  's/r.send(\&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum(), Index: new(r.raftLog.committed)})/r.send(\&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum(), Index: new(r.raftLog.lastIndex())})/'
# A follower acknowledges one entry more than the request held.
both ack-one-more raft.go \
  's/r.send(\&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum(), Index: new(mlastIndex)})/r.send(\&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum(), Index: new(mlastIndex + 1)})/'
# A candidate needs one vote fewer.
both election-without-quorum quorum/majority.go \
  's/q := len(c)\/2 + 1/q := len(c) \/ 2/'
# Node sends before it writes (application bug).
mutant sends-before-write antithesis-fm/rawnode/node.go \
  's/^\t\tearly := n.cfg.Parallel \&\& role == "leader"$/\t\tfor _, m := range rd.Messages {\n\t\t\tn.reportCause()\n\t\t\tn.cfg.Rep.Emit("send", "by", by, "msg", n.msgOf(m))\n\t\t\tn.cfg.Send(m)\n\t\t}\n\t\trd.Messages = nil\n\t\tearly := n.cfg.Parallel \&\& role == "leader"/'

# AsyncStorageWrites, node holding vote requests until written (fault E1, patches/README.md).
A="-async"
# A leader counts its own entries towards a quorum before they are on its disk.
both leader-counts-itself-before-write raft.go \
  's/r.send(\&pb.Message{To: new(r.id), Type: pb.MsgAppResp.Enum(), Index: new(li)})/if pr := r.trk.Progress[r.id]; pr != nil \&\& pr.MaybeUpdate(li) \&\& r.maybeCommit() { r.bcastAppend() }/' "$A"
# Raft hands the state machine entries that are not on disk yet.
both applies-unstable-entries rawnode.go \
  's/return !rn.asyncStorageWrites/return true/' "$A"
# Raft marks entries written when an entry of another term at the same index
# was written (see log_unstable.go stableTo). Needs a schedule seeds do not
# reach; repro/aba has it, run by scripts/aba.sh.
if [ -z "$only" ] || [ "$only" = stable-to-ignores-term ]; then
  if out=$("$here/scripts/aba.sh" 2>&1); then
    echo "ok    stable-to-ignores-term: the written schedule: $(echo "$out" | tail -1 | cut -c1-180)"
  else
    echo "FAIL  stable-to-ignores-term: $(echo "$out" | tail -2 | tr '\n' ' ' | cut -c1-200)"; fail=1
  fi
fi
# Node sends what waits for a write without waiting (application bug).
both async-sends-before-write antithesis-fm/rawnode/node.go \
  's/job = \&Write{ents: rd.Entries, snap: snap, after: hs, resp: app.GetResponses(), cause: cause, by: by, writes: write, k: -1}/job = \&Write{ents: rd.Entries, snap: snap, after: hs, cause: cause, by: by, writes: write, k: -1}\n\t\t\tfor _, m := range app.GetResponses() {\n\t\t\t\tif m.GetTo() == n.cfg.ID {\n\t\t\t\t\tjob.resp = append(job.resp, m)\n\t\t\t\t} else {\n\t\t\t\t\tout = append(out, m)\n\t\t\t\t}\n\t\t\t}/' "$A"
# Node makes its queued writes newest first (application bug).
mutant async-writes-out-of-order antithesis-fm/rawnode/node.go \
  's/\tw := n.writes\[0\]\n\tn.writes = n.writes\[1:\]/XX/; /^func (n \*Node) NextWrite/,/^}/ { s/w := n.writes\[0\]/w := n.writes[len(n.writes)-1]/; s/n.writes = n.writes\[1:\]/n.writes = n.writes[:len(n.writes)-1]/ }' "$A"
# No hold of vote requests: unpatched raft with AsyncStorageWrites (fault E1).
# Not an edit: simulator arguments only.
both upstream-vote-before-write - - "-async -nohold"

# ReadIndex reads (-reads).
# A leader gives a read index without confirming leadership with a quorum.
both read-without-quorum raft.go \
  's/if r.trk.IsVoter(r.id) \&\& r.trk.IsSingleton() {/if true {/' "-reads"
# A new leader gives a read index before it has committed an entry of its term.
both read-before-commit-in-term raft.go \
  '/case pb.MsgReadIndex:/,/sendMsgReadIndexResponse(r, m)/ s/if !r.committedEntryInCurrentTerm() {/if false {/' "-reads"

# Snapshots (-snap).
# A follower restores a snapshot although its log already matches it,
# dropping acknowledged entries.
both restore-although-log-matches raft.go \
  '/^func (r \*raft) restore(s \*pb.Snapshot) bool {/,/^}/ s/if r.raftLog.matchTerm(id) {/if false \&\& r.raftLog.matchTerm(id) {/' "-snap"
# Node labels its snapshot with the previous entry's term (application bug).
mutant snapshot-wrong-term antithesis-fm/rawnode/node.go \
  's/term, err := n.store.Term(index)$/term, err := n.store.Term(index - 1)/' "-snap"

# Node takes its own snapshot while a write installing a leader's snapshot
# is pending (application bug).
mutant snapshot-during-restore antithesis-fm/rawnode/node.go \
  's/ || n.applying || n.restoring > 0 {/ || n.applying {/' "-async -snap -steps 6000"

# One Ready for several inputs (-batch).
# A batching node sends after announcing its write, before making it (application bug).
mutant batch-sends-before-write antithesis-fm/rawnode/node.go \
  '/^func (n \*Node) Flush() {/,/^}/ s/^\t\tif write {$/\t\tfor _, m := range rd.Messages {\n\t\t\tn.cfg.Rep.Emit("send", "by", "batch", "msg", n.msgOf(m), "b", 1)\n\t\t\tn.cfg.Send(m)\n\t\t}\n\t\trd.Messages = nil\n\t\tif write {/' "-batch"
# Raft drops entries appended while earlier ones wait to be handed over for
# writing; only reachable with -batch.
mutant append-to-waiting-entries-lost log_unstable.go \
  's/^\t\tu.entries = append(u.entries, ents...)$/\t\tif len(u.entries) == 0 {\n\t\t\tu.entries = ents\n\t\t}/' "-batch"

# Membership changes (five nodes, three voters at the start).
M="-member -voters 3 -calm 4 -steps 5000"
# A leader appends a change of membership while another is not applied.
both change-while-one-waits raft.go \
  's/alreadyPending := r.pendingConfIndex > r.raftLog.applied/alreadyPending := false/' "$M"
# A node campaigns with committed, unapplied conf changes. Needs queued
# applies and -batch.
mutant campaign-before-changes-applied+batch raft.go \
  's/^\tif r.hasUnappliedConfChanges() {/\tif false \&\& r.hasUnappliedConfChanges() {/' "$M -async -batch"
# A node that is not a voter of its own configuration starts an election.
both campaign-not-a-voter raft.go \
  's/return pr != nil \&\& !pr.IsLearner \&\& !r.raftLog.hasNextOrInProgressSnapshot()/return (pr == nil || pr != nil) \&\& !r.raftLog.hasNextOrInProgressSnapshot()/' "$M"
# In a joint configuration a leader commits with a majority of the new voters only.
both joint-commit-new-voters-only quorum/joint.go \
  's/^\tidx1 := c\[1\].CommittedIndex(l)/\tidx1 := idx0/' "$M"
# In a joint configuration a candidate wins with a majority of the new voters only.
both joint-election-new-voters-only quorum/joint.go \
  's/^\tr2 := c\[1\].VoteResult(votes)/\tr2 := r1/' "$M"
# A joint change does not keep the voters there were before it.
both joint-forgets-old-voters confchange/confchange.go \
  's/^\t\toutgoing(cfg.Voters)\[id\] = struct{}{}/\t\t_ = id/' "$M"
# Node does not pass an applied change to raft (application bug).
mutant change-not-told-to-raft antithesis-fm/rawnode/node.go \
  's/^\tcs := n.rn.ApplyConfChange(cc)$/\tcs := n.Conf()\n\t_ = cc/' "$M"
# Node's snapshots carry the initial voters (application bug).
mutant snapshot-with-first-voters antithesis-fm/rawnode/node.go \
  's/ConfState: n.confState(index)}}/ConfState: n.store.first}}/' "$M -snap"
# Entries written before the commit index, node killed in between, two
# changes in a row: fault E3 (patches/README.md). Seeds do not reach it;
# repro/confsplit has the schedule, run by scripts/e3.sh.
if [ -z "$only" ] || [ "$only" = commit-index-lost-between-changes ]; then
  if out=$("$here/scripts/e3.sh" 2>&1); then
    echo "ok    commit-index-lost-between-changes: the written schedule: $(echo "$out" | sed -n 2p | cut -c1-200)"
  else
    echo "FAIL  commit-index-lost-between-changes: $(echo "$out" | grep UNEXPECTED | tr '\n' ' ' | cut -c1-300)"; fail=1
  fi
fi

# Edits not listed because no behaviour can show them:
# - follower commits to the end of its log, not of the request (log.go
#   commitTo(min(committed, l.lastIndex()))): the first accepted request
#   truncates the follower's log to where it matches the leader, so both
#   rules give the same commit index.
# - follower restores a snapshot not beyond its commit index (first check of
#   raft.restore removed): the next check (log already has the snapshot's
#   last entry) catches every such snapshot.
# - with async writes, a candidate counts its own vote before writing it:
#   other votes answer a request sent after that write, so it cannot win
#   earlier (without the hold or patch E1 it can).
exit $fail
