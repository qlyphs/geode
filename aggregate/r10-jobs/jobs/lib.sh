# lib.sh: helpers for measurement jobs. run <label> [VAR=value ...] -- <r3-cert args>: one fresh
# process under GNU time -v, with commit, binary digest, host and load before and after, and a
# 10 s sampler of the container's memory (cgroup memory.current, anon, file) and disk traffic
# (/proc/<pid>/io) in /data/out/<label>.mem.
# BIN: the build without test hooks (measurements, verification); LAB: feature lab-hooks
# (acceptance suites, prover-path comparisons). runlab is run with LAB.
BIN=/data/bin/r3-cert
LAB=/data/bin/r3-cert-lab
export R3_OUT=/data/out
header() {
  echo "# job $(basename "$0" .sh) | commit $(cat /src/COMMIT) | binary sha256 $(sha256sum "$(readlink -f $BIN)" | cut -c1-64) | lab binary sha256 $(sha256sum "$(readlink -f $LAB)" | cut -c1-64)"
  echo "# host: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | sed 's/^ //'), nproc $(nproc), cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>/dev/null), cpu.max $(cat /sys/fs/cgroup/cpu.max 2>/dev/null); $(rustc --version 2>/dev/null)"
}
sampler() {
  local out=$1
  echo "# t_utc memory.current_MiB anon_MiB file_MiB file_dirty_MiB r3_read_MiB r3_write_MiB loadavg1" >"$out"
  while true; do
    local pid
    pid=$(pgrep -n -x r3-cert || true)
    local io="0 0"
    if [ -n "$pid" ] && [ -r "/proc/$pid/io" ]; then
      io=$(awk '/^read_bytes/{r=$2}/^write_bytes/{w=$2}END{printf "%d %d", r/1048576, w/1048576}' "/proc/$pid/io")
    fi
    local st
    st=$(awk '/^anon /{a=$2}/^file /{f=$2}/^file_dirty /{d=$2}END{printf "%d %d %d", a/1048576, f/1048576, d/1048576}' /sys/fs/cgroup/memory.stat 2>/dev/null)
    echo "$(date -u +%T) $(( $(cat /sys/fs/cgroup/memory.current) / 1048576 )) $st $io $(cut -d' ' -f1 /proc/loadavg)" >>"$out"
    sleep 10
  done
}
run() {
  local label=$1; shift
  local envs=()
  while [ "$1" != "--" ]; do envs+=("$1"); shift; done
  shift
  echo "## $label | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg) | env ${envs[*]:-none} | r3-cert $*"
  sampler "/data/out/$label.mem" &
  local sp=$!
  env "${envs[@]}" /usr/bin/time -v "$BIN" "$@" 2>&1
  local rc=$?
  kill $sp 2>/dev/null
  echo "## memory: cgroup memory.peak $(( $(cat /sys/fs/cgroup/memory.peak 2>/dev/null || echo 0) / 1048576 )) MiB (container lifetime); sampled max memory.current $(awk 'NR>1 && $2>m{m=$2}END{print m+0}' /data/out/$label.mem) MiB, anon $(awk 'NR>1 && $3>m{m=$3}END{print m+0}' /data/out/$label.mem) MiB"
  echo "## end $label | exit $rc | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg)"
}
runlab() {
  local SAVED=$BIN
  BIN=$LAB
  run "$@"
  BIN=$SAVED
}
