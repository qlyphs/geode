#!/bin/bash
# entry.sh: build three r3-cert binaries (release, --locked) into the volume, record the host,
# then idle: r3-cert-base (default build of the baseline commit), r3-cert (default build of the
# commit under test) and r3-cert-lab (the same with feature lab-hooks, for the acceptance suites).
# Jobs: a process started over a remote shell does not outlive the session, so entry.sh itself
# runs the queue: `echo <job>[,<job>] > /data/req/<any name>` (start-job.sh does this) and the
# loop below starts it within 10 s, as its own child.
set -u
mkdir -p /data/logs /data/out /data/bin
C=$(cat /src/COMMIT)
B=$(cat /src/BASELINE)
exec >>/data/logs/entry.log 2>&1
echo "== start $(date -u +%FT%TZ) commit $C baseline $B"
echo "nproc $(nproc); $(grep MemTotal /proc/meminfo); cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>/dev/null); cpu.max $(cat /sys/fs/cgroup/cpu.max 2>/dev/null)"
grep -m1 'model name' /proc/cpuinfo
df -h /data /tmp | sed 's/^/df: /'
build() { # <src dir> <target dir> <out name> [features]
  local f=()
  [ -n "${4:-}" ] && f=(--features "$4")
  if [ ! -x "/data/bin/$3" ]; then
    echo "build $3 start $(date -u +%FT%TZ)"
    (cd "$1" && CARGO_HOME=/data/cargo CARGO_TARGET_DIR="$2" nice -n 5 cargo build --release --locked "${f[@]}" -j "${BUILD_JOBS:-24}" >>"/data/logs/build-$3.log" 2>&1) && cp "$2/release/r3-cert" "/data/bin/$3"
    echo "build $3 exit $? $(date -u +%FT%TZ)"
  fi
}
build /src/base/r3-cert /data/target-base "r3-cert-base-$B"
build /src/r3-cert /data/target "r3-cert-$C"
build /src/r3-cert /data/target-lab "r3-cert-lab-$C" lab-hooks
if [ -x "/data/bin/r3-cert-$C" ] && [ -x "/data/bin/r3-cert-base-$B" ]; then
  ln -sfn "/data/bin/r3-cert-base-$B" /data/bin/r3-cert-base
  ln -sfn "/data/bin/r3-cert-$C" /data/bin/r3-cert
  ln -sfn "/data/bin/r3-cert-lab-$C" /data/bin/r3-cert-lab
  for x in r3-cert-base r3-cert r3-cert-lab; do echo "$x sha256 $(sha256sum "$(readlink -f /data/bin/$x)" | cut -c1-64)"; done
  if [ -n "${JOB:-}" ]; then /src/cert-speed/run-queue.sh "$JOB" & fi
fi
echo "idle $(date -u +%FT%TZ)"
mkdir -p /data/req
while true; do
  for r in /data/req/*; do
    [ -f "$r" ] || continue
    j=$(cat "$r"); rm -f "$r"
    echo "$(date -u +%FT%TZ) request $j"
    setsid /src/cert-speed/run-queue.sh "$j" </dev/null >/dev/null 2>&1 &
  done
  sleep 10
done
