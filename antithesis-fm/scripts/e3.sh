#!/usr/bin/env bash
# Bug reproducer for fault E3 (patches/README.md): runs repro/confsplit (two
# voters added in turn; a node killed between writing an entry and writing its
# commit index) and checks each stream against the model, for:
#   checkout, Ready written atomically          -> ACCEPTED
#   checkout, entries written before HardState  -> DIVERGED, REJECTED
#   copy with patches/E3, entries then HardState -> ACCEPTED
# then the same three with one joint change (-joint). Exit 0 if all as expected.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
check() { touch "$1.eof"; "$here/tracekit/check/streamcheck.py" "$here/spec/manifest-m.json" "$1" | cut -c1-200; }
status=0
one() { # label directory-of-antithesis split expected-run expected-verdict [-joint]
  local out v
  out=$(cd "$2" && go run ./repro/confsplit ${6:-} -split "$3" -out "$work/s.ndjson" 2>&1 | grep -E 'ended|DIVERGED' | tail -1)
  rm -f "$work"/s.ndjson.*; v=$(check "$work/s.ndjson")
  if [[ "$out" == $4* && "$v" == $5* ]]; then echo "$1: $out; check: $v"
  else echo "$1: UNEXPECTED: $out; check: $v"; status=1; fi
}
one "raft as it is, one atomic write    " "$here" "" ended ACCEPTED
one "raft as it is, entries then state  " "$here" entries-hardstate DIVERGED REJECTED
rsync -a --exclude .git --exclude runs --exclude .lake --exclude target --exclude tools "$root/" "$work/src/"
for p in "$here"/patches/E3*.patch; do ( cd "$work/src" && patch -s -p1 < "$p" ) || { echo "the patch does not apply"; exit 2; }; done
one "with patches/E3, entries then state" "$work/src/antithesis-fm" entries-hardstate ended ACCEPTED
one "joint: raft as it is, one atomic write    " "$here" "" ended ACCEPTED -joint
one "joint: raft as it is, entries then state  " "$here" entries-hardstate DIVERGED REJECTED -joint
one "joint: with patches/E3, entries then state" "$work/src/antithesis-fm" entries-hardstate ended ACCEPTED -joint
exit $status
