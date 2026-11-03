# gates: the 4 GiB boundary test on an SSD-backed array, then the acceptance suite (with the
# hostile gates of the round-10 review) at N = 128 for both families.
. /src/r10-jobs/jobs/lib.sh
header
mkdir -p /tmp/spill
run bigindex H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 -- bigindex
run h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
run h9tests-128-ud H9_FAMILY=ud -- h9tests 128
