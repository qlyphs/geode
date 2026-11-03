# k10cmp: byte equality of the round-10 Keccak path (as built: fused folds on) with the reference
# Keccak prover, at N = 32 and 128 with every challenge injection, and at N = 2048.
. /src/cert-speed/jobs/lib.sh
header
runlab k10cmp-small H9_K10_HIST=1 -- k10cmp 32,128 2 0,1,2,3,4,5,6,7
runlab k10cmp-2048 H9_K10_HIST=1 -- k10cmp 2048 1 0,4,7
