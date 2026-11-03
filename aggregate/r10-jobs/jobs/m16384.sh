# m16384: chain-range certificates at N = 16384 (128 full blocks), both families, with arrays of
# at least 64 MiB stored in unlinked files on the container's local disk; fresh verification.
. /src/r10-jobs/jobs/lib.sh
header
N=16384
mkdir -p /tmp/spill
SP="H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864"
run h9chain-$N-johnson H9_FAMILY=johnson $SP -- h9chain $N
run h9chainverify-$N-johnson H9_FAMILY=johnson -- h9chainverify $N /data/out/h9chain-cert-$N-fff9110e.bin
run h9chain-$N-ud H9_FAMILY=ud $SP -- h9chain $N
run h9chainverify-$N-ud H9_FAMILY=ud -- h9chainverify $N /data/out/h9chain-cert-$N-fff9130e.bin
