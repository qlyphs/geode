# attacks: the verifier-side attacks on the N = 65536 unique-decoding certificate written by the
# commit under test (job ab); r10 ran the same attacks on its Johnson certificate.
. /src/cert-speed/jobs/lib.sh
header
run h9chainattacks-65536-ud H9_FAMILY=ud -- h9chainattacks 65536 /data/out/ab/new/h9chain-cert-65536-fff91310.bin
