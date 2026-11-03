#!/bin/bash
# start-job.sh <job>: run /src/r10-jobs/jobs/<job>.sh detached; its output goes to
# /data/out/<job>.txt (appended) and its pid to /data/out/<job>.pid.
set -eu
J=$1
[ -f "/src/r10-jobs/jobs/$J.sh" ] || { echo "no job $J"; exit 2; }
setsid nohup bash "/src/r10-jobs/jobs/$J.sh" >>"/data/out/$J.txt" 2>&1 </dev/null &
echo $! >"/data/out/$J.pid"
echo "started $J pid $!"
