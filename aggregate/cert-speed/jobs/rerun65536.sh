# rerun65536: an independent rerun of the headline result on a fresh container: the prover of
# bc4788b at N = 65,536 (unique-decoding family, disk-backed arrays), the certificate's size and
# sha256 against the recorded c9fbf852..., a fresh-process verification by the same build and by
# the baseline build, the verifier-side attacks, and the UD acceptance suite at N = 128.
. /src/cert-speed/jobs/lib.sh
header
df -h /data /tmp | sed 's/^/# df: /'
mkdir -p /data/out/rerun
f=/data/out/rerun/h9chain-cert-65536-fff91310.bin
run rerun-prove-65536 H9_FAMILY=ud H9_PROGRESS=1 $SPILL R3_OUT=/data/out/rerun -- h9chain 65536
echo "## certificate $f: $(stat -c %s "$f") bytes, sha256 $(sha256sum "$f" | cut -c1-64)"
echo "## SHA256 N=65536 ud rerun: $( [ "$(sha256sum "$f" | cut -c1-64)" = c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a ] && echo IDENTICAL || echo DIFFERENT) to the recorded c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a"
run rerun-verify-65536 H9_FAMILY=ud -- h9chainverify 65536 "$f"
runbase rerun-verify-65536-base H9_FAMILY=ud -- h9chainverify 65536 "$f"
run rerun-attacks-65536 H9_FAMILY=ud -- h9chainattacks 65536 "$f"
runlab rerun-h9tests-128-ud H9_FAMILY=ud -- h9tests 128
