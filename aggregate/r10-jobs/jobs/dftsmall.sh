# dftsmall: four-step DFT forced for every DFT of height >= 2^16 at N = 128 and 2048 (standalone
# Johnson statements), certificates compared with the default path.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/dftd /data/out/dftf
for N in 128 2048; do
  run dft-$N-default H9_FAMILY=johnson R3_OUT=/data/out/dftd -- h9 $N
  run dft-$N-fourstep H9_FAMILY=johnson H9_BIGDFT_MIN=1 R3_OUT=/data/out/dftf -- h9 $N
  echo "## N=$N default vs forced four-step DFT: $(cmp /data/out/dftd/h9-cert-$N.bin /data/out/dftf/h9-cert-$N.bin && echo IDENTICAL || echo DIFFERENT) ($(sha256sum /data/out/dftd/h9-cert-$N.bin | cut -c1-64))"
done
