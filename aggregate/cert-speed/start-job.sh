#!/bin/bash
# start-job.sh <job>[,<job>...]: queue the jobs for entry.sh's loop (see entry.sh).
set -eu
IFS=, read -ra JOBS <<<"$1"
for J in "${JOBS[@]}"; do [ -f "/src/cert-speed/jobs/$J.sh" ] || { echo "no job $J"; exit 2; }; done
mkdir -p /data/req
echo "$1" >"/data/req/$(date +%s%N)"
echo "queued $1"
