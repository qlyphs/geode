# prof: the commit under test, unique-decoding family, same runs as base-prof (N = 4096 in
# memory, N = 16384 and 65536 with arrays of at least 64 MiB disk-backed); certificates
# compared with the baseline ones of base-prof and verified in fresh processes by the baseline
# binary.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/new
for N in 4096 16384 65536; do
  lg=0; m=$N; while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
  f=h9chain-cert-$N-fff913$(printf %02x $lg).bin
  if [ $N = 4096 ]; then sp=""; else sp=$SPILL; fi
  run new-$N-ud H9_FAMILY=ud H9_PROGRESS=1 $sp R3_OUT=/data/out/new -- h9chain $N
  [ -f /data/out/base/$f ] && same /data/out/base/$f /data/out/new/$f "N=$N ud"
  runbase verify-new-$N-ud H9_FAMILY=ud -- h9chainverify $N /data/out/new/$f
done
