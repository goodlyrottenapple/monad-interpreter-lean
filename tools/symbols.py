#!/usr/bin/env python3
"""Turn `nm -S --defined-only -C` output into `addr size kind name # demangled`
with short, stable Lean-friendly names, so proofs do not depend on addresses."""
import re
import sys


def top_level_cut(s, ch):
    depth = 0
    for i, c in enumerate(s):
        if c in "<":
            depth += 1
        elif c == ">":
            depth -= 1
        elif c == ch and depth == 0:
            return i
    return len(s)


def clean(dem):
    dem = dem.replace("(anonymous namespace)::", "")
    if "operator" in dem and "(" in dem:
        s = dem[: dem.index("(", dem.index("operator") + 8)] if "operator(" not in dem else dem
        s = s[: top_level_cut(s, "(")] if "operator()" not in s else s
    else:
        s = dem[: top_level_cut(dem, "(")]
    # drop a leading return type: keep the last top-level space-separated token
    depth, last = 0, 0
    for i, c in enumerate(s):
        if c == "<":
            depth += 1
        elif c == ">":
            depth -= 1
        elif c == " " and depth == 0:
            last = i + 1
    s = s[last:]
    s = s.replace("(anonymous namespace)::", "")
    s = s.replace("monad::vm::interpreter::", "").replace("monad::vm::runtime::", "rt_")
    s = s.replace("monad::vm::", "").replace("monad::", "")
    # template arguments: keep leading integers, drop traits
    def targs(m):
        nums = re.findall(r"(?<![\w)])(\d+)u?l(?![\w])", m.group(1))
        return "".join("_" + n for n in nums)
    for _ in range(4):
        s = re.sub(r"<([^<>]*)>", targs, s)
    s = re.sub(r"[^A-Za-z0-9_]+", "_", s).strip("_")
    return "f_" + s


rows = []
for line in sys.stdin:
    parts = line.rstrip("\n").split(" ", 3)
    if len(parts) < 4 or len(parts[1]) != 16 or parts[2] not in "tTwW":
        continue
    rows.append((parts[0], parts[1], parts[2], parts[3]))
rows.sort()
seen = {}
for a, sz, k, dem in rows:
    seen.setdefault(clean(dem), []).append(a)
for a, sz, k, dem in rows:
    n = clean(dem)
    if len(set(seen[n])) > 1:
        n = f"{n}_{a[8:]}"
    print(a, sz, k, n, "#", dem)
