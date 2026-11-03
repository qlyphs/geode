# ident-gkr: the lazy-leaf GKR prover against the stored-leaf one (random leaves, every budget),
# then certificates at N = 128 and 2048, both families, with the GKR budget forced far below the
# tree size (2^8 and 2^12 entries, so most layers are recomputed) against the baseline.
. /src/cert-speed/jobs/lib.sh
header
run gkrlazy -- gkrlazy 14
mkdir -p /data/out/gkr
for fam in ud johnson; do
  case $fam in johnson) hi=11;; ud) hi=13;; esac
  for N in 128 2048; do
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    f=h9chain-cert-$N-fff9$hi$(printf %02x $lg).bin
    for b in 8 12; do
      mkdir -p /data/out/gkr/b$b
      run gkr-$N-$fam-b$b H9_FAMILY=$fam H9_GKR_LOG_BUDGET=$b R3_OUT=/data/out/gkr/b$b -- h9chain $N
      same /data/out/base/$f /data/out/gkr/b$b/$f "N=$N $fam GKR budget 2^$b"
    done
  done
done
