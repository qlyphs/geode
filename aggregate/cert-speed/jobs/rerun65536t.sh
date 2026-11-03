# rerun65536t: the prover-time rerun of the N = 65,536 UD certificate on an AMD host. One prover
# run of bc4788b with the recorded command (disk-backed arrays in /tmp/spill on the container's
# local disk), the certificate's sha256 against the recorded c9fbf852..., and a fresh-process
# verification. Each start of the job is numbered (t1, t2, ...) and writes to its own directory.
# Alongside the prover's own 5 s sampler (lib.sh) it logs host-wide vmstat every 10 s and the
# container's io and cpu pressure, to tell a disturbed run from a slow disk.
. /src/cert-speed/jobs/lib.sh
n=1; while [ -e "/data/out/t$n" ]; do n=$((n + 1)); done
o=/data/out/t$n; mkdir -p "$o"
header
echo "# run t$n; cpus: $(grep -c ^processor /proc/cpuinfo) logical, $(grep -m1 'cpu MHz' /proc/cpuinfo | cut -d: -f2 | sed 's/^ //') MHz now; cgroup cpu.weight $(cat /sys/fs/cgroup/cpu.weight 2>/dev/null)"
df -h /data /tmp | sed 's/^/# df: /'
grep -E '^(MemTotal|MemAvailable|Dirty|Writeback):' /proc/meminfo | sed 's/^/# meminfo: /'
rm -rf /tmp/spill; mkdir -p /tmp/spill
vmstat -n -t 10 >"$o/vmstat.txt" 2>&1 &
vp=$!
( while :; do echo "$(date -u +%T) io $(head -1 /sys/fs/cgroup/io.pressure 2>/dev/null) | cpu $(head -1 /sys/fs/cgroup/cpu.pressure 2>/dev/null)"; sleep 10; done ) >"$o/pressure.txt" 2>&1 &
pp=$!
f=$o/h9chain-cert-65536-fff91310.bin
run "t$n-prove-65536" H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=$o -- h9chain 65536
kill "$vp" "$pp" 2>/dev/null
mv "/data/out/t$n-prove-65536.mem" "$o/" 2>/dev/null
echo "## certificate $f: $(stat -c %s "$f") bytes, sha256 $(sha256sum "$f" | cut -c1-64)"
echo "## SHA256 N=65536 ud t$n: $( [ "$(sha256sum "$f" | cut -c1-64)" = c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a ] && echo IDENTICAL || echo DIFFERENT) to the recorded c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a"
run "t$n-verify-65536" H9_FAMILY=ud -- h9chainverify 65536 "$f"
rm -rf /tmp/spill
