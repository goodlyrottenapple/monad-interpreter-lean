#!/usr/bin/env python3
"""Print a function's instruction list from the generated Lean image, compactly.
usage: tools/show.py f_pop [f_push_1 ...]"""
import glob, re, sys
src = "".join(open(f).read() for f in sorted(glob.glob("PureInterp/Image/Text*.lean")))
for name in sys.argv[1:]:
    m = re.search(r"def %s\.prog : List Instr := \[\n(.*?)\]\n\n" % re.escape(name), src, re.S)
    print(f"-- {name}")
    for k, l in enumerate(m.group(1).split("\n")):
        l = l.strip().rstrip(",").replace("RiscvZkvm.Rv64.Instr", "").replace("(RiscvZkvm.Rv64.Reg", "")
        print(k, re.sub(r"\.(x\d+)\)", r".\1", l))
