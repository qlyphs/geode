# base-ident: baseline chain-range certificates of both families at N = 128 and 2048 (fixed
# inputs), written to /data/out/base/, with a fresh-process verification of each.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/base
for fam in ud johnson; do
  for N in 128 2048; do
    runbase base-$N-$fam H9_FAMILY=$fam R3_OUT=/data/out/base -- h9chain $N
  done
done
sha256sum /data/out/base/*.bin
