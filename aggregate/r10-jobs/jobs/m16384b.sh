# m16384b: N = 16384 Johnson chain range with the current defaults (histogram rounds on, Keccak
# working set in memory, four-step DFT, sequential readahead), two runs; fresh verification.
. /src/r10-jobs/jobs/lib.sh
header
N=16384
mkdir -p /tmp/spill
for k in 1 2; do
  run h9chain-$N-johnson-b$k H9_FAMILY=johnson H9_PROGRESS=1 H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_SPILL_SEQ=1 -- h9chain $N
done
run h9chainverify-$N-johnson-b H9_FAMILY=johnson -- h9chainverify $N /data/out/h9chain-cert-$N-fff9110e.bin
