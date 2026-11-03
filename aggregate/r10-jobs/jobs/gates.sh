# gates: the default build has no test commands; N = 4096 Johnson chain certificate from the
# default build compared with the certificate measured before the commitment-scheme rewrite
# (sha256 97f3cd10...); the 4 GiB boundary test; the acceptance suites at N = 128 (both
# families) from the lab build.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /tmp/spill /data/out/ident
run default-build-has-no-h9tests -- h9tests 32
run ident-4096 H9_FAMILY=johnson H9_K10_HIST=1 R3_OUT=/data/out/ident -- h9chain 4096
echo "## N=4096 Johnson certificate sha256 $(sha256sum /data/out/ident/h9chain-cert-4096-fff9110c.bin | cut -c1-64); before the rewrite 97f3cd102d065a2c1d6dc75cf1fd0bdfcc89bf7b8ce028db581ddc872ac755d7: $( [ "$(sha256sum /data/out/ident/h9chain-cert-4096-fff9110c.bin | cut -c1-64)" = 97f3cd102d065a2c1d6dc75cf1fd0bdfcc89bf7b8ce028db581ddc872ac755d7 ] && echo IDENTICAL || echo DIFFERENT)"
runlab bigindex H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 -- bigindex
runlab h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
runlab h9tests-128-ud H9_FAMILY=ud -- h9tests 128
