#!/bin/bash
# entry.sh: build r3-cert (release, --locked) from /src into the volume, record the host, then
# idle. Jobs are started with `/src/r10-jobs/start-job.sh <job>[,<job>]` over a remote shell
# or by setting JOB=<job> before a deploy.
set -u
mkdir -p /data/logs /data/out /data/spill /data/bin
C=$(cat /src/COMMIT)
exec >>/data/logs/entry.log 2>&1
echo "== start $(date -u +%FT%TZ) commit $C"
echo "nproc $(nproc); $(grep MemTotal /proc/meminfo); cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>/dev/null); cpu.max $(cat /sys/fs/cgroup/cpu.max 2>/dev/null)"
grep -m1 'model name' /proc/cpuinfo
df -h /data /tmp | sed 's/^/df: /'
# Leftover spill files of a killed process are already unlinked; nothing to clean there.
# Two binaries: r3-cert (no test hooks: every measurement and every verification) and
# r3-cert-lab (feature lab-hooks: the acceptance suites and the prover-path comparisons).
if [ ! -x "/data/bin/r3-cert-$C" ] || [ ! -x "/data/bin/r3-cert-lab-$C" ]; then
  echo "build start $(date -u +%FT%TZ)"
  cd /src/r3-cert && CARGO_HOME=/data/cargo CARGO_TARGET_DIR=/data/target nice -n 5 cargo build --release --locked -j "${BUILD_JOBS:-24}" >"/data/logs/build-$C.log" 2>&1
  rc=$?
  cd /src/r3-cert && CARGO_HOME=/data/cargo CARGO_TARGET_DIR=/data/target-lab nice -n 5 cargo build --release --locked --features lab-hooks -j "${BUILD_JOBS:-24}" >>"/data/logs/build-$C.log" 2>&1
  rcl=$?
  echo "build exit $rc / lab $rcl $(date -u +%FT%TZ)"
  if [ $rc -eq 0 ] && [ $rcl -eq 0 ]; then cp /data/target/release/r3-cert "/data/bin/r3-cert-$C"; cp /data/target-lab/release/r3-cert "/data/bin/r3-cert-lab-$C"; fi
fi
if [ -x "/data/bin/r3-cert-$C" ]; then
  ln -sfn "/data/bin/r3-cert-$C" /data/bin/r3-cert
  ln -sfn "/data/bin/r3-cert-lab-$C" /data/bin/r3-cert-lab
  echo "binary sha256 $(sha256sum /data/bin/r3-cert-$C | cut -c1-64); lab binary $(sha256sum /data/bin/r3-cert-lab-$C | cut -c1-64)"
  if [ -n "${JOB:-}" ]; then /src/r10-jobs/start-job.sh "$JOB"; fi
fi
echo "idle $(date -u +%FT%TZ)"
exec sleep infinity
