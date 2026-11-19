#!/usr/bin/env bash
# Runs Veil's model checker on the model of veil/EtcdRaftVeil.lean (proofs
# and PROOF-ONLY invariants removed) at the bounds of spec/MCCount<N>.cfg or
# spec/MCMemCount<N>.cfg and prints the distinct-state count, to compare with
# TLC (scripts/mc.sh MCCount<N>.cfg 900).
#
#   scripts/veil-count.sh N [LIMIT_SECONDS]     N = 2, 3, 4: three voters, no membership change
#   scripts/veil-count.sh mN [LIMIT_SECONDS]    N = 2, 3: two voters, one change adds the third
#   VEIL_SRC=file.lean                          another source file
# Without changes, chLeave is true for every value, which no leader appends
# (no joint configuration is ever entered).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
m=${1:?2, 3 or 4, or m2 or m3}; limit=${2:-900}
cfg=MCCount$m; export VEIL_FILE=${VEIL_SRC:-EtcdRaftVeil.lean}
more=", initV := fun _ => true, chAdd := fun _ => [], chRemove := fun _ => [], chJoint := fun _ => false, chLeave := fun _ => true"
case "$m" in m*)
  cfg=MCMemCount${m#m}
  more=", initV := fun s => decide (s.val < 2), chAdd := fun _ => [2], chRemove := fun _ => [], chJoint := fun _ => false, chLeave := fun _ => false" ;;
esac
bounds=$(awk '/MaxTerm|MaxLog|MaxBatch|MaxMsgs/ {printf "%s%s := %s", sep, $1, $3; sep=", "}' "$here/spec/$cfg.cfg")$more
cd "$here/veil"
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
# Build Veil and its dependencies (slow the first time).
lake build Veil > /dev/null || { echo "lake build Veil failed"; exit 2; }
tmp=Count$m.lean
trap 'rm -f "$tmp"' EXIT
python3 - "$bounds" > "$tmp" <<'PY'
import sys
import os
s = open(os.environ['VEIL_FILE']).read()
s = s[:s.index('-- Proofs.')].rsplit('\n', 2)[0]
# Bound quantifiers over terms (no term above MaxTerm + 1 is reachable).
while '-- PROOF-ONLY BEGIN' in s:                              # invariants it cannot evaluate
    a, b = s.index('-- PROOF-ONLY BEGIN'), s.index('-- PROOF-ONLY END')
    s = s[:a] + s[b + len('-- PROOF-ONLY END'):]
i, j = s.index('\ninvariant ['), s.index('\n#gen_spec')     # only in the invariants, not in lemmas
s = s[:i] + s[i:j].replace('∀ t : Nat,', '∀ t ∈ List.range (MaxTerm + 2),') + s[j:]
s = (s.replace('-- #model_check compiled', '#model_check compiled')
      .replace('--   { server := Fin 3', '  { server := Fin 3')
      .replace('--     VoteSet', '    VoteSet')
      .replace('--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2 }',
               '  { %s }' % sys.argv[1]))
assert '\n#model_check compiled' in s
print(s + '\nend EtcdRaftVeil')
PY
out=$(timeout "$limit" lake env lean "$tmp" 2>&1) && rc=0 || rc=$?
echo "$out" | grep -E 'explored|Violation' || true
[ $rc -eq 124 ] && { echo "stopped at the ${limit}s limit, no verdict"; exit 2; }
[ $rc -ne 0 ] && { echo "lean failed (exit $rc):"; echo "$out" | grep -m3 'error'; exit 1; }
exit 0
