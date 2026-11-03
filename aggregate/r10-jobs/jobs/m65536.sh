# m65536: chain range of N = 65536 (512 full blocks), Johnson family (review D.1 schedule),
# histogram rounds on, arrays of at least 64 MiB stored in unlinked files on the local disk;
# fresh verification.
. /src/r10-jobs/jobs/lib.sh
header
N=65536
mkdir -p /tmp/spill
run h9chain-$N-johnson H9_FAMILY=johnson H9_K10_HIST=1 H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 -- h9chain $N
run h9chainverify-$N-johnson H9_FAMILY=johnson -- h9chainverify $N /data/out/h9chain-cert-$N-fff91110.bin
