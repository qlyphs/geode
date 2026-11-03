# m65536ud: N = 65536 chain range, unique-decoding family; fresh verification.
. /src/r10-jobs/jobs/lib.sh
header
N=65536
rm -rf /tmp/spill; mkdir -p /tmp/spill
run h9chain-$N-ud H9_FAMILY=ud H9_PROGRESS=1 H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_SPILL_SEQ=1 -- h9chain $N
run h9chainverify-$N-ud H9_FAMILY=ud -- h9chainverify $N /data/out/h9chain-cert-$N-fff91310.bin
