#!/bin/bash
# usage: ./tlc.sh CFG [timeout-seconds] [extra TLC args]   (module MCInv.tla)
#   checks the invariants of EtcdInv.tla / EtcdReadInv.tla on a bounded instance with TLC.
#   Env: TLC_HEAP (default 5g), WORKERS (default 2). Prints TLC's output and exit=CODE.
cd "$(dirname "$0")" || exit 2
jar=$(cd ../.. && pwd)/tracekit/tools/tla2tools.jar
cfg=$1; lim=${2:-600}; shift; shift
d=$(mktemp -d)
timeout $lim java -XX:+UseParallelGC -Xmx"${TLC_HEAP:-5g}" -DTLA-Library=.. -cp "$jar" tlc2.TLC \
  -nowarning -noTE -workers ${WORKERS:-2} -metadir $d -config $cfg "$@" MCInv.tla
echo "exit=$?"
rm -rf $d
