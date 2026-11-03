# first: self checks, byte identity of the unchanged profiles, round-10 Keccak path equality at
# small N, then the acceptance suite at N = 128 for both round-10 families.
. /src/r10-jobs/jobs/lib.sh
header
run host -- host
run r10self -- r10self
run digests -- digests
run h9self -- h9self
runlab k10cmp-small -- k10cmp 32,128 2 0,1,2,3,4,5,6,7
runlab h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
runlab h9tests-128-ud H9_FAMILY=ud -- h9tests 128
