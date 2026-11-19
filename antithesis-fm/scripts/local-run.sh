#!/usr/bin/env bash
# Local run under docker compose: runs the workload for DURATION seconds
# (default 40) with the live stream check, then rechecks the recorded stream.
# Output in runs/<timestamp>/. Exit: 0 accepted, 1 not, 2 setup failure.
#
#   scripts/local-run.sh [DURATION]
# Env (same meaning as in launch.sh):
#   CHAOS=1 scripts/local-run.sh 60      # also kills, restarts, pauses and cuts off nodes
#   CHAOS=kills scripts/local-run.sh 60  # one kill every second or two
#   BUILD=0 scripts/local-run.sh         # reuse the images
#   NODES=5 scripts/local-run.sh         # five nodes (config5/)
#   PREVOTE=1 CHECK_QUORUM=1 scripts/local-run.sh   # raft's PreVote and CheckQuorum on
#   BOOT_ENTRY=0 scripts/local-run.sh    # logs start empty, at term 0
#   ASYNC=1 scripts/local-run.sh         # AsyncStorageWrites; requests for votes held
#   PATCH=E1 ASYNC=1 NO_HOLD_VOTE=1 scripts/local-run.sh   # not held, on a copy of raft with patches/E1*
#   PARALLEL=1 scripts/local-run.sh      # a leader sends before it writes
#   READ_INDEX=1 scripts/local-run.sh    # linearizable reads by raft's ReadIndex
#   SNAPSHOT_EVERY=20 scripts/local-run.sh   # a snapshot replaces the log every 20 applied entries
#   FORWARD=1 TRANSFER_RATE=0.2 BATCH=8 BATCH_WAIT=20ms MAX_INFLIGHT=2 SNAP_STATUS=1 scripts/local-run.sh
#   CONF_RATE=0.5 scripts/local-run.sh   # membership changes per second
#   NODES=5 VOTERS=raft1,raft2,raft3 CONF_RATE=0.5 STEP_DOWN=1 scripts/local-run.sh
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
duration=${1:-40}
out="$here/runs/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$out"
nodes=${NODES:-3}
all=$(seq -f etcd-raft%g 1 "$nodes" | tr '\n' ' ')
manifest=manifest; [ "$nodes" = 5 ] && manifest=manifest5
export VOTERS=${VOTERS:-} STEP_DOWN=${STEP_DOWN:-0} CONF_RATE=${CONF_RATE:-0}
if [ -n "$VOTERS" ]; then
  [ "$nodes" = 5 ] && [ "$VOTERS" = raft1,raft2,raft3 ] || { echo "VOTERS: only raft1,raft2,raft3 with NODES=5 has a configuration (spec/EtcdBindingM.cfg)"; exit 2; }
  manifest=manifest-m; export MANIFEST_NAME=-m
fi
if [ "${BOOT_ENTRY:-1}" = 0 ]; then manifest=$manifest-empty; export MANIFEST_SUFFIX=-empty; fi
export PREVOTE=${PREVOTE:-0} CHECK_QUORUM=${CHECK_QUORUM:-0} BOOT_ENTRY=${BOOT_ENTRY:-1}
export ASYNC=${ASYNC:-0} NO_HOLD_VOTE=${NO_HOLD_VOTE:-0} PARALLEL=${PARALLEL:-0} READ_INDEX=${READ_INDEX:-0} SNAPSHOT_EVERY=${SNAPSHOT_EVERY:-0}
export FORWARD=${FORWARD:-0} TRANSFER_RATE=${TRANSFER_RATE:-0} BATCH=${BATCH:-0} MAX_INFLIGHT=${MAX_INFLIGHT:-0} SNAP_STATUS=${SNAP_STATUS:-0} BATCH_WAIT=${BATCH_WAIT:-0s}
src=$here
if [ -n "${PATCH:-}" ]; then
  # Build from a copy of the tree with the patch applied.
  root=$(cd "$here/.." && pwd); copy=$(mktemp -d); trap 'rm -rf "$copy"' EXIT
  rsync -a --exclude .git --exclude runs --exclude .lake --exclude target "$root/" "$copy/"
  for p in "$here"/patches/"$PATCH"*.patch; do ( cd "$copy" && patch -s -p1 < "$p" ) || { echo "patch $p does not apply"; exit 2; }; done
  src=$copy/antithesis-fm
fi
cd "$src/config$([ "$nodes" = 5 ] && echo 5)"
export COMPOSE_FILE=docker-compose.yaml:../local/docker-compose.local.yaml
export COMPOSE_PROJECT_NAME=etcd-raft-local

docker compose down -v --remove-orphans >/dev/null 2>&1 || true
if [ "${BUILD:-1}" = 1 ]; then docker compose build -q || exit 2; fi
docker compose up -d > "$out/up.log" 2>&1 || { sleep 3; docker compose down -v >/dev/null 2>&1; docker compose up -d >> "$out/up.log" 2>&1; } \
  || { echo "could not start the cluster; see $out/up.log"; exit 2; }
docker compose exec -T driver /opt/antithesis/test/v1/main/first_start_workload
timeout 120 sh -c 'until docker compose exec -T driver grep -qs antithesis_setup /tmp/sdk.jsonl; do sleep 1; done' \
  || { echo "setup did not complete"; docker compose logs --no-color > "$out/compose.log" 2>&1; docker compose down -v >/dev/null 2>&1; exit 2; }
echo "setup complete; running for ${duration}s"

if [ "${CHAOS:-}" = kills ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep 1.$((RANDOM % 9))
      n=etcd-raft$((RANDOM % nodes + 1))
      echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker start "$n" >/dev/null
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi
if [ "${CHAOS:-}" = 1 ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep $((RANDOM % 6 + 3))
      n=etcd-raft$((RANDOM % nodes + 1))
      case $((RANDOM % 7)) in
        5|6) echo "chaos: cut $n off"; docker network disconnect "${COMPOSE_PROJECT_NAME}_default" "$n" >/dev/null; sleep $((RANDOM % 6 + 2)); docker network connect --alias "${n#etcd-}" "${COMPOSE_PROJECT_NAME}_default" "$n" >/dev/null ;;
        0) echo "chaos: restart $n"; docker restart -t 2 "$n" >/dev/null ;;
        1) echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep $((RANDOM % 4 + 1)); docker start "$n" >/dev/null ;;
        2) echo "chaos: pause $n"; docker pause "$n" >/dev/null; sleep $((RANDOM % 5 + 1)); docker unpause "$n" >/dev/null ;;
        3) echo "chaos: short pause $n"; docker pause "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker unpause "$n" >/dev/null ;;
        4) echo "chaos: kill all"; docker kill $all >/dev/null; sleep 1; docker start $all >/dev/null ;;
      esac
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi

sleep "$duration"
[ -n "${chaos:-}" ] && wait "$chaos"

# Stop the nodes so the driver has every event before the copy.
docker kill $all >/dev/null 2>&1
sleep 1
docker compose cp driver:/trace-kit "$out/kit" >/dev/null
docker compose cp driver:/tmp/sdk.jsonl "$out/sdk.jsonl" >/dev/null 2>&1
docker compose logs --no-color > "$out/compose.log" 2>&1
docker compose down -v >/dev/null 2>&1
echo "output in $out"
failed=$(jq -r 'select(.antithesis_assert.hit and (.antithesis_assert.condition | not) and .antithesis_assert.assert_type == "always") | .antithesis_assert.message' "$out/sdk.jsonl" 2>/dev/null | sort | uniq -c)
[ -n "$failed" ] && printf 'driver assertions failed:\n%s\n' "$failed"

status=0
# Result of the driver's live stream check.
live() { # label dir pattern
  local written next stopped
  written=$(wc -l < "$2/stream.ndjson" 2>/dev/null || echo 0)
  next=$(cat "$2/stream.ndjson.progress" 2>/dev/null || echo 1)
  stopped=$(grep -o "$3: .*" "$out/compose.log" | cut -c1-400)
  if [ -n "$stopped" ]; then echo "$1 live: $stopped"; return 1
  else echo "$1 live: matched $((next - 1)) of $written events and was still running"; fi
}
live kit "$out/kit" "stream check stopped" || status=1
# The recorded stream, checked again from the file.
cp "$out/kit/stream.ndjson" "$out/kit/again.ndjson"; touch "$out/kit/again.ndjson.eof"
again=$("$here/tracekit/check/streamcheck.py" "$here/spec/$manifest.json" "$out/kit/again.ndjson" | cut -c1-600)
echo "kit file: $again"
case "$again" in ACCEPTED*) ;; *) status=1 ;; esac
exit $status
