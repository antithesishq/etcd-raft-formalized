#!/usr/bin/env bash
# Bug reproducer for fault E1 (patches/README.md): runs repro/asyncvote against
# this checkout and against a copy with patches/E1 applied.
# Expected: checkout fails (two nodes apply different entries at one index);
# patched passes. Exit 0 if so.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
status=0
up=$(cd "$here" && go test -tags e1 -count=1 -v ./repro/asyncvote/ 2>&1)
if grep -q 'two nodes applied different entries' <<<"$up"; then
  echo "upstream: $(grep -o 'two nodes applied different entries.*' <<<"$up")"
else echo "upstream: UNEXPECTED: $(tail -3 <<<"$up" | tr '\n' ' ')"; status=1; fi
rsync -a --exclude .git --exclude runs --exclude .lake --exclude target --exclude tools "$root/" "$work/src/"
( cd "$work/src" && patch -s -p1 < "$here/patches/E1-vote-request-after-write.patch" ) || { echo "the patch does not apply"; exit 2; }
fx=$(cd "$work/src/antithesis-fm" && go test -tags e1 -count=1 -v ./repro/asyncvote/ 2>&1)
if grep -q '^--- PASS' <<<"$fx"; then echo "patched:  passes: $(grep -o "3's request waits.*" <<<"$fx")"
else echo "patched:  UNEXPECTED: $(tail -3 <<<"$fx" | tr '\n' ' ')"; status=1; fi
exit $status
