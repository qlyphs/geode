# ident-lazy: the self checks of the lazy provers (GKR on random leaves, tensor MLE, column-source
# sumcheck), then certificates at N = 128 and 2048, both families, with every memory budget
# forced far below the array sizes (GKR 2^8 / 2^12 entries, sumcheck columns 2^11 / 2^14), so
# that most layers and rounds take the recomputing paths, against the baseline certificates.
. /src/cert-speed/jobs/lib.sh
header
run gkrlazy -- gkrlazy 14
mkdir -p /data/out/lazy
for fam in ud johnson; do
  case $fam in johnson) hi=11;; ud) hi=13;; esac
  for N in 128 2048; do
    lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
    f=h9chain-cert-$N-fff9$hi$(printf %02x $lg).bin
    for b in "8 11" "12 14"; do
      set -- $b
      d=/data/out/lazy/g$1s$2; mkdir -p $d
      run lazy-$N-$fam-g$1s$2 H9_FAMILY=$fam H9_GKR_LOG_BUDGET=$1 H9_SC_LOG_BUDGET=$2 R3_OUT=$d -- h9chain $N
      same /data/out/base/$f $d/$f "N=$N $fam budgets GKR 2^$1 sumcheck 2^$2"
    done
  done
done
