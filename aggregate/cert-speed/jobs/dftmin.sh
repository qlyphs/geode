# dftmin: the four-step DFT for every matrix of at least 256 MiB or 64 MiB (H9_BIGDFT_MIN; the
# default is 4 GiB), so the WHIR rounds' smaller codewords are not transformed by the radix-2 path
# on disk-backed arrays; N = 16384, unique-decoding family, against the baseline certificate.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/dmin
f=h9chain-cert-16384-fff9130e.bin
for mb in 256 64; do
  run dmin-$mb-16384 H9_FAMILY=ud H9_PROGRESS=1 H9_BIGDFT_MIN=$((mb << 20)) $SPILL R3_OUT=/data/out/dmin -- h9chain 16384
  echo "## SHA256 N=16384 ud four-step from $mb MiB: $( [ "$(sha256sum /data/out/dmin/$f | cut -c1-64)" = 9d0ffb60fdbfc7276f1f722375799b8f59817b4c455d0675d4016487d49c0f01 ] && echo IDENTICAL || echo DIFFERENT) to the baseline 9d0ffb60fdbfc7276f1f722375799b8f59817b4c455d0675d4016487d49c0f01"
done
