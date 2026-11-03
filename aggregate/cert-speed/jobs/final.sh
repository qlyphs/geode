# final: the final commit on one host: identity at N = 128 and 2048 (default and forced four-step
# DFT), the acceptance suites, the baseline and the final prover alternated at N = 16384, the
# final prover at N = 65536 with a fresh verification by the baseline binary, and the verifier
# attacks on that certificate.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/fin/base /data/out/fin/new
f=h9chain-cert-16384-fff9130e.bin
runbase fin-base-16384 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/fin/base -- h9chain 16384
run fin-new-16384 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/fin/new -- h9chain 16384
same /data/out/fin/base/$f /data/out/fin/new/$f "N=16384 ud final"
f=h9chain-cert-65536-fff91310.bin
run fin-new-65536 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/fin/new -- h9chain 65536
echo "## SHA256 N=65536 ud final: $( [ "$(sha256sum /data/out/fin/new/$f | cut -c1-64)" = c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a ] && echo IDENTICAL || echo DIFFERENT) to the baseline c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a"
runbase fin-verify-65536 H9_FAMILY=ud -- h9chainverify 65536 /data/out/fin/new/$f
run fin-attacks-65536 H9_FAMILY=ud -- h9chainattacks 65536 /data/out/fin/new/$f
