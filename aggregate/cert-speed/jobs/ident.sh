# ident: certificates of the commit under test against the baseline (job base-ident) at N = 128
# and 2048, both families, chain ranges with fixed inputs; each new certificate is also verified
# in a fresh process by the baseline binary.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/new
for fam in ud johnson; do
  case $fam in johnson) hi=11;; ud) hi=13;; esac
  for N in 128 2048; do
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    f=h9chain-cert-$N-fff9$hi$(printf %02x $lg).bin
    run new-$N-$fam H9_FAMILY=$fam R3_OUT=/data/out/new -- h9chain $N
    same /data/out/base/$f /data/out/new/$f "N=$N $fam"
    runbase verify-new-$N-$fam H9_FAMILY=$fam -- h9chainverify $N /data/out/new/$f
  done
done
