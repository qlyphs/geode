"""verifier-unchanged.py <base commit> <commit>: every function whose name contains "verify" or
"verif", in every source file of aggregate/r3-cert/src, has the same text at both commits; files
that hold only verifier or transcript code (pcs.rs, mmcs10.rs, fs7.rs, reg7.rs, registry.rs) are
unchanged as a whole. Prints one line per function and a verdict."""
import re, subprocess, sys

base, head = sys.argv[1], sys.argv[2]
root = "aggregate/r3-cert/src/"

def show(rev, path):
    r = subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None

def files(rev):
    out = subprocess.run(["git", "ls-tree", "--name-only", rev, root], capture_output=True, text=True).stdout
    return [l for l in out.split() if l.endswith(".rs")]

def functions(src):
    # Top-level and impl-level fn items: from the signature line to the matching closing brace.
    out = {}
    for m in re.finditer(r"^[ \t]*(?:pub(?:\([a-z]+\))? )?fn ([A-Za-z0-9_]+)", src, re.M):
        name, i = m.group(1), src.index("{", m.end())
        depth, j = 0, i
        while True:
            c = src[j]
            depth += (c == "{") - (c == "}")
            j += 1
            if depth == 0:
                break
        out.setdefault(name, []).append(src[m.start():j])
    return out

ok = True
for path in sorted(set(files(base)) | set(files(head))):
    a, b = show(base, path), show(head, path)
    name = path[len(root):]
    if name in ("pcs.rs", "mmcs10.rs", "fs7.rs", "reg7.rs", "registry.rs"):
        same = a == b
        ok &= same
        print(f"{'same' if same else 'CHANGED'}  whole file {name}")
        continue
    if a is None or b is None:
        print(f"note  {name} exists at one commit only")
        continue
    fa, fb = functions(a), functions(b)
    for fn in sorted(k for k in fa if "verif" in k):
        same = fa[fn] == fb.get(fn)
        ok &= same
        print(f"{'same' if same else 'CHANGED'}  {name}::{fn}")
print("VERIFIER CODE UNCHANGED" if ok else "VERIFIER CODE CHANGED")
