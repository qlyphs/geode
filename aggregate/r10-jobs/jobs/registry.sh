# registry: the round registry of the round-10 lab profiles, both families: N = 128 and 2048
# with an honest prove/verify run checked round by round, N = 4096, 16384, 65536 from the
# enforced table. One file per (N, profile) in /data/out/registry/.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/registry
for fam in johnson ud; do
  for N in 128 2048 4096 16384 65536; do
    case $fam in johnson) hi=10;; ud) hi=12;; esac
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    pid=$(printf 'fff9%s%02x' $hi $lg)
    out=/data/out/registry/r10-registry-$N-$pid.txt
    arg=""; [ $N -le 2048 ] && arg=run
    echo "## registry N=$N family $fam -> $out | $(date -u +%FT%TZ)"
    { header; H9_FAMILY=$fam /usr/bin/time -v $BIN h9registry $N $arg; } >"$out" 2>&1
    echo "## end registry N=$N family $fam exit $? | $(date -u +%FT%TZ)"
  done
done
