#!/bin/bash
# start-job.sh <job>[,<job>...]: run /src/r10-jobs/jobs/<job>.sh one after the other,
# detached; each job's output goes to /data/out/<job>.txt (appended); the queue's pid is in
# /data/out/queue.pid and its progress in /data/out/queue.log.
set -eu
IFS=, read -ra JOBS <<<"$1"
for J in "${JOBS[@]}"; do [ -f "/src/r10-jobs/jobs/$J.sh" ] || { echo "no job $J"; exit 2; }; done
setsid nohup bash -c 'for J in "$@"; do echo "$(date -u +%FT%TZ) start $J" >>/data/out/queue.log; bash "/src/r10-jobs/jobs/$J.sh" >>"/data/out/$J.txt" 2>&1 </dev/null; echo "$(date -u +%FT%TZ) end $J exit $?" >>/data/out/queue.log; done' queue "${JOBS[@]}" >/dev/null 2>&1 </dev/null &
echo $! >/data/out/queue.pid
echo "started ${JOBS[*]} pid $!"
