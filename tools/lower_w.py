#!/usr/bin/env python3
"""Rewrite RV64 word instructions that riscv-zkvm does not model.

Reads GCC assembly on stdin and writes assembly on stdout in which every
ADDW/SUBW/MULW/SLLIW/SRLIW/SRAIW (and the NEGW alias) is replaced by an
equivalent sequence of 64-bit instructions plus ADDIW (`sext.w`), which the
model does have. Each replacement only writes the original destination
register, so no scratch register is needed.

This pass is not trusted: the proof is about the final linked binary.
"""
import re
import sys

REG = r"([a-z][a-z0-9]+)"
OPS3 = {"addw": "add", "subw": "sub", "mulw": "mul"}
UNSUPPORTED = {"sllw", "srlw", "sraw", "divw", "divuw", "remw", "remuw"}


def lower(line):
    m = re.match(r"^(\s+)(\w+)\s+(.*)$", line)
    if not m:
        return [line]
    ind, op, args = m.group(1), m.group(2), [a.strip() for a in m.group(3).split(",")]
    if op in UNSUPPORTED:
        sys.exit(f"lower_w: unsupported word instruction: {line.strip()}")
    if op in OPS3 and len(args) == 3:
        rd, a, b = args
        return [f"{ind}{OPS3[op]}\t{rd},{a},{b}\n", f"{ind}addiw\t{rd},{rd},0\n"]
    if op == "negw" and len(args) == 2:
        rd, a = args
        return [f"{ind}sub\t{rd},zero,{a}\n", f"{ind}addiw\t{rd},{rd},0\n"]
    if op == "slliw" and len(args) == 3:
        rd, a, sh = args
        return [f"{ind}slli\t{rd},{a},{sh}\n", f"{ind}addiw\t{rd},{rd},0\n"]
    if op in ("srliw", "sraiw") and len(args) == 3:
        rd, a, sh = args
        sh = int(sh, 0)
        shift = "srli" if op == "srliw" else "srai"
        out = [f"{ind}slli\t{rd},{a},32\n", f"{ind}{shift}\t{rd},{rd},{32 + sh}\n"]
        if op == "srliw" and sh == 0:
            out.append(f"{ind}addiw\t{rd},{rd},0\n")
        return out
    return [line]


for line in sys.stdin:
    sys.stdout.writelines(lower(line))
