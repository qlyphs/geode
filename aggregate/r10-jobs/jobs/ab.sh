# ab: histogram rounds off / on, alternated, two runs each, at N = 2048 and 4096 (Johnson chain
# ranges); the certificates of each size are compared byte for byte.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/ab-off /data/out/ab-on
for N in 2048 4096; do
  for k in 1 2; do
    run ab-$N-off-$k H9_FAMILY=johnson H9_K10_HIST=0 R3_OUT=/data/out/ab-off -- h9chain $N
    run ab-$N-on-$k H9_FAMILY=johnson H9_K10_HIST=1 R3_OUT=/data/out/ab-on -- h9chain $N
  done
  f=h9chain-cert-$N-fff911$(printf %02x $( [ $N = 2048 ] && echo 11 || echo 12 )).bin
  echo "## N=$N histogram off / on certificates: $(cmp /data/out/ab-off/$f /data/out/ab-on/$f && echo IDENTICAL || echo DIFFERENT)"
done
