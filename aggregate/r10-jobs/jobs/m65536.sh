# m65536: chain range of N = 65536 (512 full blocks), Johnson family (review D.1 schedule),
# histogram rounds on, arrays of at least 64 MiB in unlinked files on the local disk with
# sequential readahead, four-step DFT for codewords of 4 GiB or more; live phase progress on
# stderr; fresh verification.
. /src/r10-jobs/jobs/lib.sh
header
N=65536
rm -rf /tmp/spill; mkdir -p /tmp/spill
run h9chain-$N-johnson H9_FAMILY=johnson H9_PROGRESS=1 H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_SPILL_SEQ=1 -- h9chain $N
run h9chainverify-$N-johnson H9_FAMILY=johnson -- h9chainverify $N /data/out/h9chain-cert-$N-fff91110.bin
