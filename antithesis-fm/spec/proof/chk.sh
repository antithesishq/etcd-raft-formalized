#!/bin/bash
# usage: chk.sh Module [l1 l2]   -- check one module (or lines l1..l2 of it) with tlapm; print failures
#   TLAPM    the tlapm binary (default: tlapm on PATH)
#   THREADS  prover threads (default 2)
#   MEM_KB   virtual-memory cap for tlapm and its provers (default 24 GB; Isabelle needs about that)
# Full output in /tmp/etcd-raft-chk-Module.out.
cd "$(dirname "$0")" || exit 2
f=$1; shift
if [ $# -ge 2 ]; then R="--toolbox $1 $2"; else R=""; fi
out=/tmp/etcd-raft-chk-$f.out
ulimit -v "${MEM_KB:-24000000}"
"${TLAPM:-tlapm}" -I .. --threads "${THREADS:-2}" $(./flags.sh "$f") $R "$f.tla" > "$out" 2>&1
if [ -n "$R" ]; then
  grep -c "@!!status:proved" "$out" | sed 's/^/proved: /'
  grep -B6 "@!!status:failed" "$out" | grep "@!!loc" | sort -u
else
  grep "ERROR\|^File\|proved" "$out" | grep -v "Could not" | head -40
fi
