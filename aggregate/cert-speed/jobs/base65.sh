# base65: the baseline at N = 65536 (unique-decoding family, disk-backed arrays) on the host of
# the final run, for a same-host comparison.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/fin/base
runbase fin-base-65536 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/fin/base -- h9chain 65536
sha256sum /data/out/fin/base/h9chain-cert-65536-fff91310.bin
