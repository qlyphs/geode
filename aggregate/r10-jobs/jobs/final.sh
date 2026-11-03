# final: the round registries of both families from the default build (honest prove/verify
# check at N = 128 and 2048), the unique-decoding N = 2048 standalone certificate, and the
# sha256 of every measured certificate.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/final/registry /data/out/final/ud2048
for fam in johnson ud; do
  case $fam in johnson) hi=10;; ud) hi=12;; esac
  for N in 128 2048 4096 16384 65536; do
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    arg=""; [ $N -le 2048 ] && arg=run
    out=/data/out/final/registry/r10-registry-$N-fff9$hi$(printf %02x $lg).txt
    { header; H9_FAMILY=$fam /usr/bin/time -v $BIN h9registry $N $arg; } >"$out" 2>&1
    echo "## registry N=$N $fam exit $? -> $out"
  done
done
run h9-2048-ud H9_FAMILY=ud R3_OUT=/data/out/final/ud2048 -- h9 2048
echo "## certificate digests"
sha256sum /data/out/final/ud2048/h9-cert-2048.bin /data/out/dftd/h9-cert-128.bin /data/out/dftd/h9-cert-2048.bin /data/out/h9chain-cert-*.bin
ls -l /data/out/final/ud2048/h9-cert-2048.bin /data/out/dftd/h9-cert-*.bin /data/out/h9chain-cert-*.bin
