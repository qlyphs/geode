# ident-dft: the DFT self checks (both four-step paths against p3), then certificates at N = 128
# and 2048, both families, with the four-step DFT forced for every DFT of height >= 2^16
# (H9_BIGDFT_MIN=1; even heights take the in-place path), against the baseline certificates.
. /src/cert-speed/jobs/lib.sh
header
run r10self -- r10self
mkdir -p /data/out/dft
for fam in ud johnson; do
  case $fam in johnson) hi=11;; ud) hi=13;; esac
  for N in 128 2048; do
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    f=h9chain-cert-$N-fff9$hi$(printf %02x $lg).bin
    run dft-$N-$fam H9_FAMILY=$fam H9_BIGDFT_MIN=1 R3_OUT=/data/out/dft -- h9chain $N
    same /data/out/base/$f /data/out/dft/$f "N=$N $fam four-step forced"
  done
done
