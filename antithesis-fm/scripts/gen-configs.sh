#!/usr/bin/env bash
# Writes spec/*.cfg and spec/manifest*.json from the tables below. The files
# are committed (the driver image and scripts read them); edit them here.
# scripts/validator-tests.sh fails if they differ from this script.
#
#   scripts/gen-configs.sh           write them
#   scripts/gen-configs.sh --check   write nothing; exit 1 if a file differs or is not in a table
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
out="$here/spec"; check=0
if [ "${1:-}" = --check ]; then check=1; out=$(mktemp -d); trap 'rm -rf "$out"' EXIT; fi

# Trace spec configs (3 or 5 nodes, Bootstrapped or empty log) and their manifests.
binding() { # config-name manifest-name servers Bootstrapped voters-at-the-start
  cat > "$out/$1.cfg" <<END
SPECIFICATION TraceSpec
CONSTANTS
  Server = {$3}
  InitVoters = {$5}
  Values = {"v"}
  Nil = ""
  Bootstrapped = $4
INVARIANTS
  ElectionSafety
  OneVotePerTerm
  Safe
ALIAS Alias
CHECK_DEADLOCK FALSE
END
  cat > "$out/$2.json" <<END
{
  "stream_spec": "EtcdBinding.tla",
  "stream_config": "$1.cfg",
  "tools": "../tracekit/tools",
  "classes": "../tracekit/stream/classes",
  "library": [
    "../tracekit/tla"
  ]
}
END
}
three='"raft1", "raft2", "raft3"'; five="$three, \"raft4\", \"raft5\""
binding EtcdBinding       manifest        "$three" TRUE  "$three"
binding EtcdBindingEmpty  manifest-empty  "$three" FALSE "$three"
binding EtcdBinding5      manifest5       "$five"  TRUE  "$five"
binding EtcdBinding5Empty manifest5-empty "$five"  FALSE "$five"
# Membership changes: five nodes, of which three are voters at the start.
binding EtcdBindingM      manifest-m      "$five"  TRUE  "$three"
binding EtcdBindingMEmpty manifest-m-empty "$five" FALSE "$three"

# Bounded instances (MCEtcd.tla), for scripts/mc.sh.
safety="ElectionSafety OneVotePerTerm LogMatching CommitSafety StateMachineSafety LeaderCompleteness
  CommittedEntriesPreserved LeaderLogIsLed RequestsFromLed ConfirmedWithinLog"
reads="ReadIndexSafety ReadMsgsOld ReadFloorOld ReadFloorBound"
steps="TermMonotonic CommitMonotonic"
confs="ConfIsCommitted LeaderConf"
mc() { # name spec MaxTerm MaxLog MaxBatch MaxMsgs symmetry(y|n) substitutions(;-separated) invariants properties [voters] [servers]
  { echo "SPECIFICATION $2"; echo "CONSTANTS"
    echo "  Server = {${12:-s1, s2, s3}}"; echo "  InitVoters = {${11:-s1, s2, s3}}"; echo "  Values = {v1}"; echo "  Nil = Nil"
    echo "  MaxTerm = $3"; echo "  MaxLog = $4"; echo "  MaxBatch = $5"; echo "  MaxMsgs = $6"
    echo "$8" | tr ';' '\n' | sed 's/^ */  /'
    echo "CONSTRAINT Bounded"; [ "$7" = n ] || echo "SYMMETRY Symmetry"
    echo "INVARIANTS"; for i in $9; do echo "  $i"; done
    if [ -n "${10}" ]; then echo "PROPERTIES"; for i in ${10}; do echo "  $i"; done; fi
    echo "CHECK_DEADLOCK FALSE"; } > "$out/$1.cfg"
}
fixed="ConfChanges <- NoChanges"; member="ConfChanges <- SmallChanges"
#  name           spec         T L B M  sym substitutions                     invariants        properties
# Fixed membership, unrestricted Spec with a read index; state counts compared
# with Veil (scripts/veil-count.sh).
mc MCCount2       Spec         2 2 1 2  n "$fixed"                            "$safety $reads"  ""
mc MCCount3       Spec         2 2 1 3  n "$fixed"                            "$safety $reads"  ""
mc MCCount4       Spec         1 1 1 6  n "$fixed"                            "$safety $reads"  ""
# Without restarts, with restarts, and random simulation.
mc MCTiny5        QuietSpec    2 2 1 6  y "$fixed"                            "$safety"         "$steps NoAppliesSkipped"
mc MCTiny7        QuietSpec    1 2 1 7  y "$fixed"                            "$safety"         "$steps NoAppliesSkipped"
mc MCFullTiny5    FullSpec     2 2 1 5  y "$fixed"                            "$safety"         "$steps NoAppliesSkipped"
mc MCSim          FullSpec     3 3 2 16 n "$fixed"                            "$safety"         "$steps NoAppliesSkipped"
# Reaches the bootstrapped start state (NotBooted is expected to be violated).
mc MCBoot         FullSpec     1 1 1 5  y "$fixed"                            "NotBooted"       ""
# Membership changes: two nodes (one initial voter), three voters, random
# simulation. Not exhaustive within the limits; the proofs cover membership.
mc MCMemTwo       FullSpec     2 2 1 5  y "$member"                           "$safety $confs"  "$steps NoAppliesSkipped" "s1" "s1, s2"
mc MCMem3         FullSpec     2 2 1 5  y "$member"                           "$safety $confs"  "$steps NoAppliesSkipped" "s1, s2, s3"
mc MCMemSim       FullSpec     4 4 2 24 n "$member"                           "$safety $confs"  "$steps NoAppliesSkipped" "s1, s2"

# One change adding a third node to two voters; state counts compared with
# Veil (scripts/veil-count.sh m2, m3).
mc MCMemCount2    Spec         2 2 1 2  n "ConfChanges <- OneChange"          "$safety $confs $reads"  "" "s1, s2"
mc MCMemCount3    Spec         2 2 1 3  n "ConfChanges <- OneChange"          "$safety $confs $reads"  "" "s1, s2"
# A read index with membership changes: bounded (FullSpec restrictions) and
# random simulation.
mc MCReadMem3     FullReadSpec 2 2 1 4  y "ConfChanges <- OneChange"          "$safety $confs $reads"  "" "s1, s2"
mc MCReadMemTwo   FullReadSpec 2 2 1 5  y "$member"                           "$safety $confs $reads"  "" "s1" "s1, s2"
mc MCReadMemSim   FullReadSpec 4 4 2 24 n "$member"                           "$safety $confs $reads"  "" "s1, s2"

if [ $check = 1 ]; then
  rc=0
  for f in "$out"/*; do cmp -s "$f" "$here/spec/$(basename "$f")" || { echo "spec/$(basename "$f") differs from scripts/gen-configs.sh"; rc=1; }; done
  for f in "$here"/spec/*.cfg "$here"/spec/manifest*.json; do [ -e "$out/$(basename "$f")" ] || { echo "spec/$(basename "$f") is not in scripts/gen-configs.sh"; rc=1; }; done
  exit $rc
fi
