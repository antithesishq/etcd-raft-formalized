#!/usr/bin/env bash
# Runs the simulator (sim/) on seeds FIRST..LAST and checks each stream against
# the model. Prints each stream not accepted (kept on disk) and a count.
# Exit 0 if every stream was accepted.
#
#   scripts/sim-batch.sh FIRST LAST [NODES] [STEPS]     e.g. 1 200 3 3000
#   KEEP=dir scripts/sim-batch.sh ...                   keep every stream there
#   BOOT=0 scripts/sim-batch.sh ...                     logs start empty, at term 0
#   SIMARGS=-prevote scripts/sim-batch.sh ...           PreVote and CheckQuorum on
#   SIMARGS=-async scripts/sim-batch.sh ...             AsyncStorageWrites, vote requests held until written
#   SIMARGS="-async -nohold" scripts/sim-batch.sh ...   no hold: rejected (fault E1, patches/README.md)
#   PATCH=E1 SIMARGS="-async -nohold" scripts/sim-batch.sh ...   no hold, on a copy with patches/E1* applied
#   SIMARGS=-parallel scripts/sim-batch.sh ...          a leader sends before it writes
#   VOTERS=3 SIMARGS=-member scripts/sim-batch.sh 1 200 5   membership changes, 3 of 5 voters at start
#   JOBS=8 scripts/sim-batch.sh ...
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
first=${1:?first seed}; last=${2:?last seed}; nodes=${3:-3}; steps=${4:-3000}
out=${KEEP:-$here/runs/sim/$(date +%Y%m%d-%H%M%S)}
mkdir -p "$out"
if [ -n "${PATCH:-}" ]; then
  root=$(cd "$here/.." && pwd); src=$(mktemp -d); trap 'rm -rf "$src"' EXIT
  rsync -a --exclude .git --exclude runs --exclude .lake --exclude target --exclude tools "$root/" "$src/"
  for p in "$here"/patches/"$PATCH"*.patch; do ( cd "$src" && patch -s -p1 < "$p" ) || { echo "patch $p does not apply"; exit 2; }; done
  ( cd "$src/antithesis-fm" && go build -o "$out/sim" ./sim ) || exit 2
else
  ( cd "$here" && go build -o "$out/sim" ./sim ) || exit 2
fi
boot=${BOOT:-1}
manifest="$here/spec/manifest$([ "$nodes" = 5 ] && echo 5)$([ "$boot" = 1 ] || echo -empty).json"
if [ -n "${VOTERS:-}" ]; then
  [ "$nodes" = 5 ] && [ "$VOTERS" = 3 ] || { echo "VOTERS: only 3 of 5 nodes has a configuration (spec/EtcdBindingM.cfg)"; exit 2; }
  manifest="$here/spec/manifest-m$([ "$boot" = 1 ] || echo -empty).json"
fi
one() {
  seed=$1; f="$out/$nodes-$seed.ndjson"
  sim=$("$out/sim" -seed "$seed" -nodes "$nodes" -steps "$steps" -boot="$([ "$boot" = 1 ] && echo true || echo false)" ${VOTERS:+-voters $VOTERS} ${SIMARGS:-} -out "$f" 2>&1); rc=$?
  touch "$f.eof"
  v=$("$here/tracekit/check/streamcheck.py" "$manifest" "$f" | cut -c1-700)
  case "$v" in
    ACCEPTED*) [ $rc -eq 0 ] && { echo ok; [ -z "${KEEP:-}" ] && rm -f "$f" "$f".*; return; } ;;
  esac
  echo "seed $seed nodes $nodes: sim: $sim; check: $v"
}
export -f one; export out nodes steps manifest here boot KEEP SIMARGS VOTERS
seq "$first" "$last" | xargs -P "${JOBS:-$(nproc)}" -I{} bash -c 'one {}' > "$out/verdicts"
bad=$(grep -vc '^ok$' "$out/verdicts")
grep -v '^ok$' "$out/verdicts" | sort | head -40
echo "$(grep -c '^ok$' "$out/verdicts") of $((last - first + 1)) accepted [$out]"
[ "$bad" -eq 0 ]
