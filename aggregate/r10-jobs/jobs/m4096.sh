# m4096: chain-range certificates at N = 4096 (32 full blocks). Johnson family: round-10 Keccak
# path without and with histogram rounds, and the reference Keccak path (all three certificates
# compared byte for byte); unique-decoding family; every certificate verified in a fresh process.
. /src/r10-jobs/jobs/lib.sh
header
N=4096
J=/data/out/h9chain-cert-$N-fff9110c.bin
mkdir -p /data/out/ref /data/out/hist
run h9chain-$N-johnson-1 H9_FAMILY=johnson H9_K10_HIST=0 -- h9chain $N
run h9chainverify-$N-johnson-1 H9_FAMILY=johnson -- h9chainverify $N $J
run h9chain-$N-johnson-hist H9_FAMILY=johnson H9_K10_HIST=1 R3_OUT=/data/out/hist -- h9chain $N
run h9chain-$N-johnson-reference-keccak H9_FAMILY=johnson H9_K10=0 R3_OUT=/data/out/ref -- h9chain $N
echo "## r10 / r10+histogram / reference Keccak path certificates: $(cmp $J /data/out/hist/$(basename $J) && cmp $J /data/out/ref/$(basename $J) && echo IDENTICAL || echo DIFFERENT) ($(sha256sum $J | cut -c1-64))"
run h9chain-$N-johnson-2 H9_FAMILY=johnson H9_K10_HIST=0 -- h9chain $N
run h9chainverify-$N-johnson-2 H9_FAMILY=johnson -- h9chainverify $N $J
run h9chain-$N-ud H9_FAMILY=ud -- h9chain $N
run h9chainverify-$N-ud H9_FAMILY=ud -- h9chainverify $N /data/out/h9chain-cert-$N-fff9130c.bin
