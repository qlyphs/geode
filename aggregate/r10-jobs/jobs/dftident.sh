# dftident: four-step DFT self checks, then the N = 4096 Johnson chain certificate with every
# DFT of height >= 2^16 forced through the four-step path, compared with the reference
# certificate (sha256 97f3cd10...).
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /data/out/dft
run r10self -- r10self
run dft-4096 H9_FAMILY=johnson H9_BIGDFT_MIN=1 R3_OUT=/data/out/dft -- h9chain 4096
echo "## N=4096 four-step-DFT certificate sha256 $(sha256sum /data/out/dft/h9chain-cert-4096-fff9110c.bin | cut -c1-64): $( [ "$(sha256sum /data/out/dft/h9chain-cert-4096-fff9110c.bin | cut -c1-64)" = 97f3cd102d065a2c1d6dc75cf1fd0bdfcc89bf7b8ce028db581ddc872ac755d7 ] && echo IDENTICAL || echo DIFFERENT) to the reference certificate"
