# attrib: which of the two DFT changes removes the commit's re-reads at N = 16384 (odd height):
# the final prover with the in-place transform off, then with the page-cache hints off.
. /src/cert-speed/jobs/lib.sh
header
mkdir -p /data/out/attr
f=h9chain-cert-16384-fff9130e.bin
run attr-noinplace-16384 H9_FAMILY=ud H9_PROGRESS=1 H9_BIGDFT_INPLACE=0 $SPILL R3_OUT=/data/out/attr -- h9chain 16384
echo "## SHA256 N=16384 in-place off: $( [ "$(sha256sum /data/out/attr/$f | cut -c1-64)" = 9d0ffb60fdbfc7276f1f722375799b8f59817b4c455d0675d4016487d49c0f01 ] && echo IDENTICAL || echo DIFFERENT)"
run attr-noadvise-16384 H9_FAMILY=ud H9_PROGRESS=1 H9_BIGDFT_ADVISE=0 $SPILL R3_OUT=/data/out/attr -- h9chain 16384
echo "## SHA256 N=16384 hints off: $( [ "$(sha256sum /data/out/attr/$f | cut -c1-64)" = 9d0ffb60fdbfc7276f1f722375799b8f59817b4c455d0675d4016487d49c0f01 ] && echo IDENTICAL || echo DIFFERENT)"
