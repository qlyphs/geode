# base-prof: baseline profile, unique-decoding family: N = 16384 and 65536 with the r10 defaults
# (arrays of at least 64 MiB disk-backed), then N = 4096 with and without disk-backed arrays.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/base
runbase base-4096-ud-mem H9_FAMILY=ud H9_PROGRESS=1 R3_OUT=/data/out/base -- h9chain 4096
runbase base-16384-ud H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/base -- h9chain 16384
runbase base-65536-ud H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/base -- h9chain 65536
sha256sum /data/out/base/*.bin
