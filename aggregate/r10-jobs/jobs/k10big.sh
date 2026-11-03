# k10big: byte equality of the round-10 Keccak path with histogram rounds on, at N = 32 and 128
# (every injection), and at N = 2048 with and without histogram rounds.
. /src/r10-jobs/jobs/lib.sh
header
runlab k10cmp-small-hist H9_K10_HIST=1 -- k10cmp 32,128 2 0,1,2,3,4,5,6,7
runlab k10cmp-2048 H9_K10_HIST=0 -- k10cmp 2048 1 0,4,7
runlab k10cmp-2048-hist H9_K10_HIST=1 -- k10cmp 2048 1 0,4,7
