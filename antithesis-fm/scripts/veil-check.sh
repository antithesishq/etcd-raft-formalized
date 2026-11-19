#!/usr/bin/env bash
# Checks the proofs of veil/EtcdRaftVeil.lean in parallel: action sections
# (`-- <Name>` after `-- Proofs.`) are dealt into JOBS files, each prefixed by
# the model, and each file is run with `lake env lean`.
#
#   scripts/veil-check.sh [JOBS] [LIMIT_SECONDS_PER_FILE]   default: min(actions, cores); 3600 s
#   PER_ACTION=1 scripts/veil-check.sh ...                  one file per action
#   ONLY="Restart Ack" scripts/veil-check.sh ...            only these actions
#   VEIL_FILE=other.lean                                    another source file
#
# Prints per file: ok/FAIL/TIMEOUT, time, first failing goal; then a total.
# Lean output and files go to runs/veil/. Exit 0 only if every file is ok
# (no error, no `sorry`, no timeout).
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
jobs=${1:-$(nproc)}; limit=${2:-3600}
cd "$here/veil"
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
# Build Veil and its dependencies (slow the first time).
lake build Veil > /dev/null || { echo "lake build Veil failed"; exit 2; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"; rm -f "$here"/veil/Check_*.lean' EXIT
python3 - "$tmp" "$jobs" "${PER_ACTION:-}" "${ONLY:-}" <<'PY'
import re, sys
import os
s = open(os.environ.get('VEIL_FILE', 'EtcdRaftVeil.lean')).read()
i = s.index('-- Proofs.')
head, proofs = s[:i].rsplit('\n', 2)[0], s[i:]
G = r'(?:prove_veil_invariant_goal|prove_goal_unregistered)'  # the second: see veil/EtcdRaftVeil.lean
names = re.findall(r'\n-- (\w+)\n\n' + G, proofs)
everything = len(re.findall(r'\n' + G + ' ', proofs))
only = sys.argv[4].split()
n = len(names) if sys.argv[3] else min(int(sys.argv[2]), len(names))
groups = [[] for _ in range(n)]
total = 0
if only:
    assert set(only) <= set(names), 'no such action'
for k, a in enumerate(names):
    body = re.search(r'\n-- %s\n\n(.*?)(?=\n-- \w+\n\n%s|\nend EtcdRaftVeil)' % (a, G), proofs, re.S).group(1)
    total += len(re.findall(G + ' ', body))
    if not only or a in only:
        groups[k % n].append((a, body))
assert total == everything, 'a proof is outside every action section'
groups = [g for g in groups if g]
total = sum(len(re.findall(G + ' ', b)) for g in groups for _, b in g)
n = len(groups)
labels = []
for k, g in enumerate(groups):
    label = g[0][0] if len(g) == 1 else 'g%d' % (k + 1)
    labels.append(label)
    open('Check_%s.lean' % label, 'w').write(head + '\n' + '\n\n'.join(b for _, b in g) + '\n\nend EtcdRaftVeil\n')
    open('%s/%s.sections' % (sys.argv[1], label), 'w').write(' '.join(a for a, _ in g))
open(sys.argv[1] + '/names', 'w').write('\n'.join(labels) + '\n')
print('%d proofs of %d actions in %d files' % (total, sum(len(g) for g in groups), n))
open(sys.argv[1] + '/jobs', 'w').write(str(n))
PY
one() {
  a=$1; s=$(date +%s)
  timeout "$limit" lake env lean "Check_$a.lean" > "$tmp/$a.out" 2>&1; rc=$?
  e=$(( $(date +%s) - s ))
  if [ $rc -eq 124 ]; then st=TIMEOUT
  elif [ $rc -ne 0 ] || grep -q ': error' "$tmp/$a.out" || grep -q 'sorry' "$tmp/$a.out"; then st=FAIL
  else st=ok; fi
  why=""
  if [ $st = FAIL ]; then
    ln=$(grep -m1 ': error' "$tmp/$a.out" | cut -d: -f2)
    [ -n "$ln" ] && why=$(head -n "$ln" "Check_$a.lean" | grep -E '^(prove_veil_invariant_goal|prove_goal_unregistered)' | tail -1 | cut -d' ' -f2,3)
    why="first failure: ${why:-?}: $(grep -m1 ': error' "$tmp/$a.out" | cut -d: -f4- | cut -c1-80)"
  fi
  mkdir -p "$here/runs/veil" && cp "$tmp/$a.out" "$here/runs/veil/$a.out" && cp "Check_$a.lean" "$here/runs/veil/$a.lean"
  echo "$st $a ${e}s ($(cat "$tmp/$a.sections")) $why"
}
export -f one; export limit tmp here
jobs=$(cat "$tmp/jobs")
xargs -P "$jobs" -I{} bash -c 'one {}' < "$tmp/names" | tee "$tmp/all"
bad=$(grep -vc '^ok ' "$tmp/all")
echo "$(grep -c '^ok ' "$tmp/all") of $(wc -l < "$tmp/names") files ok"
[ "$bad" -eq 0 ]
