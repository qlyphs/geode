# tests128: library schedules of both families, then the acceptance suite at N = 128 for both.
. /src/r10-jobs/jobs/lib.sh
header
run sched -- sched
run h9tests-128-johnson H9_FAMILY=johnson -- h9tests 128
run h9tests-128-ud H9_FAMILY=ud -- h9tests 128
