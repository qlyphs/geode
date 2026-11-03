# lib.sh: helpers for measurement jobs. run <label> [VAR=value ...] -- <r3-cert args>: one fresh
# process of $BIN under GNU time -v, with the binary digest, host and load before and after, and
# a 5 s sampler of the container's memory (cgroup memory.current, anon, file, dirty), the
# process's disk traffic (/proc/<pid>/io) and CPU time in /data/out/<label>.mem.
# BASE: default build of the baseline commit; NEW: default build of the commit under test;
# LAB: the commit under test with feature lab-hooks (acceptance suites). runbase / runlab run
# with BASE / LAB.
BASE=/data/bin/r3-cert-base
NEW=/data/bin/r3-cert
LAB=/data/bin/r3-cert-lab
BIN=$NEW
export R3_OUT=/data/out
mkdir -p /tmp/spill
header() {
  echo "# job $(basename "$0" .sh) | commit $(cat /src/COMMIT) baseline $(cat /src/BASELINE)"
  for x in BASE NEW LAB; do eval "p=\$$x"; echo "# $x $(readlink -f "$p") sha256 $(sha256sum "$(readlink -f "$p")" | cut -c1-64)"; done
  echo "# host: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | sed 's/^ //'), nproc $(nproc), cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>/dev/null), cpu.max $(cat /sys/fs/cgroup/cpu.max 2>/dev/null); $(rustc --version 2>/dev/null)"
}
sampler() {
  local out=$1 pid=$2
  echo "# t_utc memory.current_MiB anon_MiB file_MiB file_dirty_MiB read_MiB write_MiB utime_s stime_s loadavg1" >"$out"
  while kill -0 "$pid" 2>/dev/null; do
    local c io="0 0" cpu="0 0"
    c=$(pgrep -P "$pid" | head -1)
    if [ -n "$c" ] && [ -r "/proc/$c/io" ]; then
      io=$(awk '/^read_bytes/{r=$2}/^write_bytes/{w=$2}END{printf "%d %d", r/1048576, w/1048576}' "/proc/$c/io")
      cpu=$(awk -v hz="$(getconf CLK_TCK)" '{printf "%.0f %.0f", $14/hz, $15/hz}' "/proc/$c/stat")
    fi
    local st
    st=$(awk '/^anon /{a=$2}/^file /{f=$2}/^file_dirty /{d=$2}END{printf "%d %d %d", a/1048576, f/1048576, d/1048576}' /sys/fs/cgroup/memory.stat 2>/dev/null)
    echo "$(date -u +%T) $(( $(cat /sys/fs/cgroup/memory.current) / 1048576 )) $st $io $cpu $(cut -d' ' -f1 /proc/loadavg)" >>"$out"
    sleep 5
  done
}
run() {
  local label=$1; shift
  local envs=()
  while [ "$1" != "--" ]; do envs+=("$1"); shift; done
  shift
  echo "## $label | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg) | bin $(basename "$(readlink -f "$BIN")") | env ${envs[*]:-none} | r3-cert $*"
  env "${envs[@]}" /usr/bin/time -v "$BIN" "$@" 2>&1 &
  local tp=$!
  sampler "/data/out/$label.mem" "$tp" &
  local sp=$!
  wait "$tp"
  local rc=$?
  kill "$sp" 2>/dev/null
  echo "## memory: cgroup memory.peak $(( $(cat /sys/fs/cgroup/memory.peak 2>/dev/null || echo 0) / 1048576 )) MiB (container lifetime); sampled max memory.current $(awk 'NR>1 && $2>m{m=$2}END{print m+0}' /data/out/$label.mem) MiB, anon $(awk 'NR>1 && $3>m{m=$3}END{print m+0}' /data/out/$label.mem) MiB"
  echo "## end $label | exit $rc | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg)"
}
runbase() { local S=$BIN; BIN=$BASE; run "$@"; BIN=$S; }
runlab() { local S=$BIN; BIN=$LAB; run "$@"; BIN=$S; }
# same <a> <b> <what>: one line comparing two files by sha256.
same() {
  local a b
  a=$(sha256sum "$1" | cut -c1-64); b=$(sha256sum "$2" | cut -c1-64)
  echo "## SHA256 $3: $( [ "$a" = "$b" ] && echo IDENTICAL || echo DIFFERENT) baseline $a new $b"
}
SPILL="H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_SPILL_SEQ=1"
