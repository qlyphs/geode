# spillcmp: SSD-backed arrays against anonymous memory at N = 128 and 2048 (standalone lab
# statements, Johnson family): the two certificates must be byte-identical.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/mem /data/out/ssd /tmp/spill
for N in 128 2048; do
  run h9-$N-memory H9_FAMILY=johnson R3_OUT=/data/out/mem -- h9 $N
  run h9-$N-ssd H9_FAMILY=johnson R3_OUT=/data/out/ssd H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=1048576 -- h9 $N
  echo "## N=$N memory vs SSD-backed certificates: $(cmp /data/out/mem/h9-cert-$N.bin /data/out/ssd/h9-cert-$N.bin && echo IDENTICAL || echo DIFFERENT) ($(sha256sum /data/out/mem/h9-cert-$N.bin | cut -c1-64))"
done
