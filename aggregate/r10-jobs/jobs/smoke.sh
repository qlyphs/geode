# smoke: round-10 self checks, byte identity of QLYAUTH3/4/7 and the Keccak kernel, h9tests at
# N = 128 for both round-10 families.
. /src/r10-jobs/jobs/lib.sh
header
run host -- host
run r10self -- r10self
run digests -- digests
run h9self -- h9self
runlab h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
runlab h9tests-128-ud H9_FAMILY=ud -- h9tests 128
