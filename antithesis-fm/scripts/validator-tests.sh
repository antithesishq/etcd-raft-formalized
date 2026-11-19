#!/usr/bin/env bash
# Tests of the stream check: gen-configs.sh --check passes; every stream under
# traces/ is accepted (manifest chosen from the name: 5 -> five nodes, m- ->
# 3 of 5 voters with membership changes, -empty -> logs start empty); every
# mutation of mutate.py, applied to the first stream with a place for it, is
# REJECTED or VIOLATED at or after the changed event. Exit 0 if all pass.
#
#   scripts/validator-tests.sh
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
manifest() { # trace directory name -> manifest
  local m=manifest
  case "$1" in m-*) m=${m}-m ;; *5*) m=${m}5 ;; esac
  case "$1" in *-empty) m=$m-empty ;; esac
  echo "$here/spec/$m.json"
}
verdict() { # stream trace-name -> "VERDICT index rest"
  cp "$1" "$tmp/s.ndjson"; rm -f "$tmp"/s.ndjson.*; touch "$tmp/s.ndjson.eof"
  "$here/tracekit/check/streamcheck.py" "$(manifest "$2")" "$tmp/s.ndjson" 2>&1
}
if out=$("$here/scripts/gen-configs.sh" --check 2>&1); then echo "ok    the configurations of spec/ are those of scripts/gen-configs.sh"
else echo "FAIL  $(echo "$out" | tr '\n' ';' | cut -c1-300)"; fail=1; fi
streams=("$here"/traces/*/stream.ndjson)
for f in "${streams[@]}"; do
  out=$(verdict "$f" "$(basename "$(dirname "$f")")")
  case "$out" in
    ACCEPTED*) echo "ok    accept $(basename "$(dirname "$f")"): $out" ;;
    *) echo "FAIL  accept $(basename "$(dirname "$f")"): $(echo "$out" | cut -c1-200)"; fail=1 ;;
  esac
done
for m in $("$here/scripts/mutate.py" list); do
  at=""
  for f in "${streams[@]}"; do
    at=$("$here/scripts/mutate.py" "$m" "$f" "$tmp/$m.ndjson") && break
    at=""
  done
  if [ -z "$at" ]; then echo "FAIL  $m: no recorded stream has a place for it"; fail=1; continue; fi
  out=$(verdict "$tmp/$m.ndjson" "$(basename "$(dirname "$f")")")
  v=$(echo "$out" | awk '{print $1}'); k=$(echo "$out" | awk '{print $2}')
  if { [ "$v" = REJECTED ] || [ "$v" = VIOLATED ]; } && [ "$k" -ge "$at" ]; then
    echo "ok    reject $m: changed at $at ($(basename "$(dirname "$f")")); $(echo "$out" | cut -c1-60)"
  else
    echo "FAIL  reject $m: changed at $at ($(basename "$(dirname "$f")")); $(echo "$out" | cut -c1-200)"; fail=1
  fi
done
exit $fail
