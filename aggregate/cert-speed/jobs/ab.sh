# ab: baseline and commit under test alternated in one container (same host, same disk),
# unique-decoding family: N = 4096 in memory (twice each), N = 16384 disk-backed (twice each),
# N = 65536 disk-backed (once each). Every certificate pair is compared by sha256 and every new
# certificate is verified in a fresh process by the baseline binary.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/ab/base /data/out/ab/new
pair() { # <N> <k> <spill env or empty>
  local N=$1 k=$2 sp=$3 lg=0 m=$1
  while [ $m -gt 1 ]; do m=$((m/2)); lg=$((lg+1)); done
  local f=h9chain-cert-$N-fff913$(printf %02x $lg).bin
  runbase ab-base-$N-$k H9_FAMILY=ud H9_PROGRESS=1 $sp R3_OUT=/data/out/ab/base -- h9chain $N
  run ab-new-$N-$k H9_FAMILY=ud H9_PROGRESS=1 $sp R3_OUT=/data/out/ab/new -- h9chain $N
  same /data/out/ab/base/$f /data/out/ab/new/$f "N=$N ud run $k"
  runbase ab-verify-new-$N-$k H9_FAMILY=ud -- h9chainverify $N /data/out/ab/new/$f
}
pair 4096 1 ""
pair 4096 2 ""
pair 16384 1 "$SPILL"
pair 16384 2 "$SPILL"
pair 65536 1 "$SPILL"
