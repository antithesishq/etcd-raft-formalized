#!/bin/bash
# usage: final.sh [Module...]  -- clean check (--cleanfp --strict) of the given modules, default all
# in dependency order. Appends one line per module to final.log; full output in final-Module.log.
#   TLAPM, THREADS, MEM_KB as in chk.sh.
cd "$(dirname "$0")" || exit 2
[ $# -eq 0 ] && set -- EtcdRec EtcdChange EtcdBase EtcdActs EtcdType EtcdGrow EtcdLog \
                       EtcdSimple1 EtcdSimple2 EtcdSimple3 EtcdMember EtcdLC EtcdCommitBase \
                       EtcdCommit EtcdAckBase EtcdAck EtcdReadCore EtcdReadStep EtcdSafety
ulimit -v "${MEM_KB:-24000000}"
log=final.log
status=0
for f in "$@"; do
  s=$(date +%s)
  "${TLAPM:-tlapm}" -I .. --threads "${THREADS:-2}" $(./flags.sh "$f") --cleanfp --strict "$f.tla" > "final-$f.log" 2>&1 || status=1
  echo "$f $(( $(date +%s) - s ))s: $(grep -oE 'All [0-9]+ obligations? proved|[0-9]+/[0-9]+ obligations failed' "final-$f.log" | tail -1)" | tee -a "$log"
done
echo "DONE $* (exit $status)" | tee -a "$log"
exit $status
