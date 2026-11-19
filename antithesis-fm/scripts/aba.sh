#!/usr/bin/env bash
# Bug reproducer: runs repro/aba (a write overtaken by entries of a later term
# at the same index) against this checkout and against a copy with the term
# check in unstable.stableTo disabled (mutant stable-to-ignores-term of
# sut-mutants.sh), and checks both streams against the model.
# Expected: checkout ACCEPTED, mutant REJECTED. Exit 0 if so.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
check() { touch "$1.eof"; "$here/tracekit/check/streamcheck.py" "$here/spec/manifest5.json" "$1" | cut -c1-260; }
status=0
( cd "$here" && go run ./repro/aba -out "$work/up.ndjson" ) > /dev/null || { echo "the schedule does not run"; exit 2; }
up=$(check "$work/up.ndjson")
case "$up" in ACCEPTED*) echo "raft as it is:   $up" ;; *) echo "raft as it is:   UNEXPECTED: $up"; status=1 ;; esac
rsync -a --exclude .git --exclude runs --exclude .lake --exclude target --exclude tools "$root/" "$work/src/"
sed -i 's/if gt != id.term {/if false \&\& gt != id.term {/' "$work/src/log_unstable.go"
cmp -s "$work/src/log_unstable.go" "$root/log_unstable.go" && { echo "the edit did not apply"; exit 2; }
mut=$( cd "$work/src/antithesis-fm" && go run ./repro/aba -out "$work/mut.ndjson" 2>&1 | tail -1 | cut -c1-200 )
v=$(check "$work/mut.ndjson")
case "$v" in REJECTED*|VIOLATED*) echo "with the bug:    $v" ;; *) echo "with the bug:    UNEXPECTED: $v ($mut)"; status=1 ;; esac
exit $status
