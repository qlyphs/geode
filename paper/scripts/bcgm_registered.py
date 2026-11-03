"""BCGM fallback bounds (H4 fallback) at every registered Johnson schedule.

ledger10.py prints the BCGM rows for N = 128, 2,048 and 65,536 at the registered schedules but at a
non-registered candidate for N = 16,384 and not at all for N = 4,096. This script reuses
ledger10.py's own functions (no new formula) at the five registered Johnson schedules of the round
registries and writes paper/data/bcgm-registered.txt. Run from the repository root:
python3 paper/scripts/bcgm_registered.py
"""
import os
import types

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
LEDGER = os.path.join(ROOT, "aggregate", "r10-security", "ledger10.py")
L = types.ModuleType("ledger10")
L.__file__ = LEDGER
exec(compile(open(LEDGER).read(), "ledger10.py", "exec"), L.__dict__)

# Registered Johnson schedules and F_q pool slacks, from the registries' census and coin lines.
REG = [
    (128, (4, [7, 9, 11], [6, 5, 4, 4]), 589),
    (2048, (2, [5, 8, 10], [6, 5, 5, 5]), 656),
    (4096, (2, [4, 7, 10], [6, 5, 5, 5]), 728),
    (16384, (1, [2, 5, 8, 11], [6, 5, 5, 5, 5]), 1158),
    (65536, (1, [2, 5, 8, 11], [6, 5, 5, 5, 5]), 2878),
]
out = ["# BCGM fallback (BCGM 2025/2051 Theorem 9.2 constant in place of DKT26 Theorem 5.12), registered Johnson schedules",
       "# computed with ledger10.py profile_report(regime='JB-BCGM'); R = 2^64, classical CF24 form, E = 2^20"]
for n, sch, slack in REG:
    dkt = L.profile_report("JB", n, sch, regime="JB", qslack=slack)
    r = L.profile_report("BCGM", n, sch, regime="JB-BCGM", qslack=slack)
    out.append(f"N = {n:6d} {str(sch):34s}: BCGM eps_max {L.fmt(r['eps_max'])}, classical E=2^20 {L.fmt(r['cl_max_1048576'])} "
               f"(sum: {L.fmt(r['cl_sum_1048576'])}); DKT26 classical E=2^20 {L.fmt(dkt['cl_max_1048576'])}")
path = os.path.join(ROOT, "paper", "data", "bcgm-registered.txt")
open(path, "w").write("\n".join(out) + "\n")
print("\n".join(out))
