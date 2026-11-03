# advise: the page-cache hints of the four-step DFT, on and off, against the baseline, at
# N = 16384 (odd height: two-array path) and 65536 (even height: in-place path), unique-decoding
# family, disk-backed arrays; certificates compared with the baseline's.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/adv/base /data/out/adv/on /data/out/adv/off
f=h9chain-cert-16384-fff9130e.bin
runbase adv-base-16384 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/adv/base -- h9chain 16384
run adv-on-16384 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/adv/on -- h9chain 16384
same /data/out/adv/base/$f /data/out/adv/on/$f "N=16384 ud hints on"
run adv-off-16384 H9_FAMILY=ud H9_PROGRESS=1 H9_BIGDFT_ADVISE=0 $SPILL R3_OUT=/data/out/adv/off -- h9chain 16384
same /data/out/adv/base/$f /data/out/adv/off/$f "N=16384 ud hints off"
f=h9chain-cert-65536-fff91310.bin
run adv-on-65536 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/adv/on -- h9chain 65536
echo "## SHA256 N=65536 ud hints on: $( [ "$(sha256sum /data/out/adv/on/$f | cut -c1-64)" = c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a ] && echo IDENTICAL || echo DIFFERENT) to the baseline c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a"
runbase adv-verify-on-65536 H9_FAMILY=ud -- h9chainverify 65536 /data/out/adv/on/$f
