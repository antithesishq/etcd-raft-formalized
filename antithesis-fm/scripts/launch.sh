#!/usr/bin/env bash
# Builds, validates (snouty validate) and launches the workload on Antithesis.
# Prints the run's id on its last line.
#
#   scripts/launch.sh COMPUTE_HOURS ["description"]
# Env (defaults off):
#   UNFILTERED=1 scripts/launch.sh 50   # keep the printed stream in the run's events
#   TIER=standard scripts/launch.sh 50  # performance tier: turbo (default), fast, standard
#   VARIANT=name scripts/launch.sh 50   # recorded on the run, e.g. for a seeded bug
#   BUILD=0 scripts/launch.sh 50        # the images are built already (a seeded bug)
#   CONFIG=config5 scripts/launch.sh 50 # five nodes
#   PREVOTE=1 CHECK_QUORUM=1 scripts/launch.sh 50   # raft's PreVote and CheckQuorum on
#   BOOT_ENTRY=0 scripts/launch.sh 50   # logs start empty, at term 0
#   ASYNC=1 scripts/launch.sh 50        # AsyncStorageWrites; vote requests held until written
#   PATCH=E1 ASYNC=1 NO_HOLD_VOTE=1 scripts/launch.sh 50   # not held, on a copy of raft with patches/E1*
#   PARALLEL=1 scripts/launch.sh 50     # a leader sends before it writes
#   READ_INDEX=1 scripts/launch.sh 50   # linearizable reads by raft's ReadIndex, not through the log
#   SNAPSHOT_EVERY=20 scripts/launch.sh 50   # a snapshot replaces the log every 20 applied entries
#   FORWARD=1 scripts/launch.sh 50      # followers pass proposals on to the leader
#   TRANSFER_RATE=0.05 scripts/launch.sh 50  # the driver asks for leadership to be handed over, per second
#   BATCH=8 BATCH_WAIT=20ms scripts/launch.sh 50   # one Ready per up to 8 inputs, waiting 20 ms
#   MAX_INFLIGHT=2 scripts/launch.sh 50 # raft's MaxInflightMsgs
#   SNAP_STATUS=1 scripts/launch.sh 50  # raft is told whether each snapshot it sent arrived
#   CONF_RATE=0.2 scripts/launch.sh 50  # the driver asks for changes of membership, per second
#   CONFIG=config5 VOTERS=raft1,raft2,raft3 CONF_RATE=0.2 scripts/launch.sh 50   # 3 of 5 voters
#   STEP_DOWN=1 ...                     # a leader that applies its own removal stops leading
set -euo pipefail
hours=${1:?usage: launch.sh COMPUTE_HOURS [description]}
desc=${2:-"etcd-raft formalized: etcd-io/raft checked step by step against a small-step TLA+ model"}
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/.." && pwd)
export SNOUTY_CONTAINER_ENGINE=${SNOUTY_CONTAINER_ENGINE:-docker}

# PATCH: launch from a copy of the tree with patches/$PATCH* applied.
if [ -n "${PATCH:-}" ]; then
  src=$(mktemp -d); trap 'rm -rf "$src"' EXIT
  rsync -a --exclude .git --exclude runs --exclude .lake --exclude target "$repo/" "$src/"
  for p in "$here"/patches/"$PATCH"*.patch; do ( cd "$src" && patch -s -p1 < "$p" ) || { echo "patch $p does not apply"; exit 2; }; done
  REV=$(git -C "$repo" rev-parse --short HEAD) BRANCH=$(git -C "$repo" rev-parse --abbrev-ref HEAD) \
    VARIANT="${VARIANT:-patch-$PATCH}" PATCH= "$src/antithesis-fm/scripts/launch.sh" "$@"
  exit $?
fi

# The printed stream is suppressed during fuzzing unless UNFILTERED=1.
filter='^trace-kit '
[ "${UNFILTERED:-}" = 1 ] && filter='^no-such-line$'

mkdir -p "$here/runs"
cd "$here/${CONFIG:-config}"
# Wait while other containers named etcd-raft1.., etcd-raft-driver exist.
for _ in $(seq 120); do
  docker ps -a --format '{{.Names}}' | grep -qxE 'etcd-raft([1-5]|-driver)' || break
  sleep 15
done
# Settings go into .env beside the compose file; Antithesis does not see this shell's env.
suffix=""; [ "${BOOT_ENTRY:-1}" = 0 ] && suffix=-empty
# Stream-check manifest: all nodes voters, or raft1-3 of five (-m).
manifest=5
if [ -n "${VOTERS:-}" ]; then
  [ "${CONFIG:-config}" = config5 ] && [ "$VOTERS" = raft1,raft2,raft3 ] || { echo "VOTERS: only raft1,raft2,raft3 with CONFIG=config5 has a configuration (spec/EtcdBindingM.cfg)"; exit 2; }
  manifest=-m
fi
printf 'PREVOTE=%s\nCHECK_QUORUM=%s\nBOOT_ENTRY=%s\nMANIFEST_SUFFIX=%s\nASYNC=%s\nNO_HOLD_VOTE=%s\nPARALLEL=%s\nREAD_INDEX=%s\nSNAPSHOT_EVERY=%s\nFORWARD=%s\nTRANSFER_RATE=%s\nBATCH=%s\nMAX_INFLIGHT=%s\nSNAP_STATUS=%s\nBATCH_WAIT=%s\nVOTERS=%s\nSTEP_DOWN=%s\nCONF_RATE=%s\nMANIFEST_NAME=%s\n' \
  "${PREVOTE:-0}" "${CHECK_QUORUM:-0}" "${BOOT_ENTRY:-1}" "$suffix" "${ASYNC:-0}" "${NO_HOLD_VOTE:-0}" "${PARALLEL:-0}" "${READ_INDEX:-0}" "${SNAPSHOT_EVERY:-0}" \
  "${FORWARD:-0}" "${TRANSFER_RATE:-0}" "${BATCH:-0}" "${MAX_INFLIGHT:-0}" "${SNAP_STATUS:-0}" "${BATCH_WAIT:-0s}" \
  "${VOTERS:-}" "${STEP_DOWN:-0}" "${CONF_RATE:-0}" "$manifest" > .env
trap 'rm -f "$here/${CONFIG:-config}/.env"' EXIT
[ "${BUILD:-1}" = 1 ] && docker compose -p etcd-raft-launch -f docker-compose.yaml build
# Retry validation if container names are taken.
for try in 1 2 3 4 5; do
  snouty validate . --timeout 5m > "$here/runs/validate.log" 2>&1 && break
  grep -q 'is already in use' "$here/runs/validate.log" && [ "$try" != 5 ] || { cat "$here/runs/validate.log"; exit 1; }
  sleep 60
done

# A copied tree has no git: REV and BRANCH are passed in.
rev=${REV:-$(git -C "$repo" rev-parse --short HEAD)}
branch=${BRANCH:-$(git -C "$repo" rev-parse --abbrev-ref HEAD)}
SNOUTY_UNSTABLE_FEATURES=teams snouty launch \
  --json \
  --launcher basic_test \
  --no-vcs \
  --config . \
  --source etcd-raft \
  --test-name "etcd-raft-formalized $branch" \
  --description "$desc" \
  --fault-tolerance high_availability \
  --fault-exclusions '^(etcd-raft-)?driver$' \
  --max-compute-hours "$hours" \
  --performance-tier "${TIER:-turbo}" \
  --filter-logs-matching "$filter" \
  --param attrs.variant="${VARIANT:-upstream}" \
  --param attrs.prevote="${PREVOTE:-0}" \
  --param attrs.check_quorum="${CHECK_QUORUM:-0}" \
  --param attrs.boot_entry="${BOOT_ENTRY:-1}" \
  --param attrs.async="${ASYNC:-0}" \
  --param attrs.no_hold_vote="${NO_HOLD_VOTE:-0}" \
  --param attrs.parallel="${PARALLEL:-0}" \
  --param attrs.read_index="${READ_INDEX:-0}" \
  --param attrs.snapshot_every="${SNAPSHOT_EVERY:-0}" \
  --param attrs.forward="${FORWARD:-0}" \
  --param attrs.transfer_rate="${TRANSFER_RATE:-0}" \
  --param attrs.batch="${BATCH:-0}" \
  --param attrs.batch_wait="${BATCH_WAIT:-0s}" \
  --param attrs.max_inflight="${MAX_INFLIGHT:-0}" \
  --param attrs.snap_status="${SNAP_STATUS:-0}" \
  --param attrs.voters="${VOTERS:-all}" \
  --param attrs.conf_rate="${CONF_RATE:-0}" \
  --param attrs.step_down="${STEP_DOWN:-0}" \
  --param attrs.config="${CONFIG:-config}" \
  --param attrs.workload=etcd-raft-formalized \
  --param attrs.raft_rev="$rev"
