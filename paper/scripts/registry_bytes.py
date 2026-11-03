"""Certificate bytes fixed by the verifier round registries, for every registered N and family.

Each registry row states the body bytes of one registered round. The certificate is the manifest
(512 B), the public c_tilde (64 N), the hint counts (N), the commitment root (64 B), the round bodies,
and the remaining WHIR proof data (Merkle openings and framing), whose length depends on the query
indices. This script sums the bodies, adds the fixed public parts, and, where an honest run is
recorded in the registry, derives the remaining WHIR bytes as total minus fixed. It writes
paper/data/registry-bytes.txt. Run from the repository root: python3 paper/scripts/registry_bytes.py
"""
import os
import re

# The registries read by ledger10.py; byte-identical to aggregate/r3-cert/transcripts/r10-registry-*.txt.
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
REG_DIR = os.path.join(ROOT, "aggregate", "r10-security", "registry")
FILES = [(128, "J", "fff91007"), (128, "U", "fff91207"), (2048, "J", "fff9100b"), (2048, "U", "fff9120b"),
         (4096, "J", "fff9100c"), (4096, "U", "fff9120c"), (16384, "J", "fff9100e"), (16384, "U", "fff9120e"),
         (65536, "J", "fff91010"), (65536, "U", "fff91210")]
out = ["# fixed = 512 manifest + 64 N c_tilde + N hint counts + 64 root + sum of registered round bodies",
       "# rest = measured total - fixed (WHIR Merkle openings and framing); '-' where the registry records no honest run"]
for n, fam, pid in FILES:
    body, total = 0, None
    text = open(os.path.join(REG_DIR, f"r10-registry-{n}-{pid}.txt")).read()
    for line in text.split("\n"):
        if re.match(r"^\d+ \|", line):
            cells = [c.strip() for c in line.split("|")]
            if cells[9].isdigit():
                body += int(cells[9])
        m = re.search(r"honest certificate (\d+) B", line)
        if m:
            total = int(m.group(1))
    fixed = 512 + 64 * n + n + 64 + body
    rest = "-" if total is None else f"{total - fixed}"
    tot = "-" if total is None else f"{total}"
    out.append(f"N = {n:6d} family {fam} profile 0x{pid}: bodies {body} B, fixed {fixed} B = {fixed / n:.2f} B/sig, "
               f"measured total {tot} B, rest {rest} B")
path = os.path.join(ROOT, "paper", "data", "registry-bytes.txt")
open(path, "w").write("\n".join(out) + "\n")
print("\n".join(out))
