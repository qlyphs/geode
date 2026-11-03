# suites: the acceptance suites of both families at N = 128 (lab build of the commit under
# test), the self checks, and the default build has no test command.
. /src/cert-speed/jobs/lib.sh
header
run default-build-has-no-h9tests -- h9tests 32
run h9self -- h9self
run r10self -- r10self
run gkrlazy -- gkrlazy 14
runlab h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
runlab h9tests-128-ud H9_FAMILY=ud -- h9tests 128
