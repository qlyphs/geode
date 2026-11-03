# lib.sh: helpers for measurement jobs. run <label> [VAR=value ...] -- <r3-cert args>: one fresh
# process under GNU time -v, with commit, binary digest, host and load before and after.
BIN=/data/bin/r3-cert
export R3_OUT=/data/out
header() {
  echo "# job $(basename "$0" .sh) | commit $(cat /src/COMMIT) | binary sha256 $(sha256sum "$(readlink -f $BIN)" | cut -c1-64)"
  echo "# host: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | sed 's/^ //'), nproc $(nproc), cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>/dev/null), cpu.max $(cat /sys/fs/cgroup/cpu.max 2>/dev/null); $(rustc --version 2>/dev/null)"
}
run() {
  local label=$1; shift
  local envs=()
  while [ "$1" != "--" ]; do envs+=("$1"); shift; done
  shift
  echo "## $label | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg) | env ${envs[*]:-none} | r3-cert $*"
  env "${envs[@]}" /usr/bin/time -v "$BIN" "$@" 2>&1
  echo "## end $label | exit $? | $(date -u +%FT%TZ) | load $(cut -d' ' -f1-3 /proc/loadavg)"
}
