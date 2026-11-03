#!/bin/bash
# run-queue.sh <job>[,<job>...]: run /src/cert-speed/jobs/<job>.sh one after the other; each job's
# output goes to /data/out/<job>.txt (appended), the queue's progress to /data/out/queue.log.
IFS=, read -ra JOBS <<<"$1"
# One queue at a time: a later request waits for the running one (never two provers at once).
exec 9>/data/out/queue.lock
flock 9
echo $$ >/data/out/queue.pid
for J in "${JOBS[@]}"; do
  [ -f "/src/cert-speed/jobs/$J.sh" ] || { echo "$(date -u +%FT%TZ) no job $J" >>/data/out/queue.log; continue; }
  echo "$(date -u +%FT%TZ) start $J" >>/data/out/queue.log
  bash "/src/cert-speed/jobs/$J.sh" >>"/data/out/$J.txt" 2>&1 </dev/null
  echo "$(date -u +%FT%TZ) end $J exit $?" >>/data/out/queue.log
done
