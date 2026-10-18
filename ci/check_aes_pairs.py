#!/usr/bin/env python3
"""Checks that the generated AArch64 code keeps each AES round's two
instructions next to each other, from the generated code in
`src/asm/aarch64/`.

A round of AES on AArch64 is two instructions: `aese vD, vK` (AddRoundKey,
SubBytes, ShiftRows), then `aesmc vD, vD` (MixColumns), and `aesd` then
`aesimc` to decrypt. Arm's cores (the Cortex-A and Neoverse cores, whose
Software Optimization Guides describe it) and Apple's fuse the two into one
operation only when the `aesmc` is the instruction right after its `aese`
and takes the `aese`'s destination. A pair split by another instruction runs
as two, which made the interleaved AES-GCM loop of
pyca/verified-garbage#2758 slower than the code it replaced. The proofs say
nothing about timing, so this script checks it: an `aese vD` whose result is
next used by an `aesmc` of `vD`, in the same straight-line code, must be
followed by that `aesmc` immediately. An `aese` whose result is used
otherwise (a final round, or `SubWord` in the key schedule) is not a pair.
"""

import pathlib
import re
import sys

from check_mcdt import FN, code

ROOT = pathlib.Path(__file__).resolve().parent.parent
ASM = ROOT / "src" / "asm"
TARGET = "aarch64"

MIX = {"aese": "aesmc", "aesd": "aesimc"}
# A SIMD register in any of its forms: `v1.16b`, `q1`, `d1`, `s1`, ….
REG = re.compile(r"\b[vqdsbh](\d+)\b")
BRANCHES = {"b", "bl", "blr", "br", "ret", "cbz", "cbnz", "tbz", "tbnz"}


def mnemonic(instr):
    """The mnemonic, without a condition (`b.ne` is `b`)."""
    return instr.split(None, 1)[0].split(".", 1)[0]


def registers(instr):
    """The numbers of the SIMD registers `instr` names, in order (the
    destination first)."""
    parts = instr.split(None, 1)
    return [int(n) for n in REG.findall(parts[1] if len(parts) > 1 else "")]


def check_function(name, instrs, lines, labels):
    """The errors of one function, and how many pairs it has."""
    starts = {d for defs in labels.values() for d in defs}
    errors = []
    pairs = 0
    for i, instr in enumerate(instrs):
        op = mnemonic(instr)
        if op not in MIX:
            continue
        dst = registers(instr)[0]
        for j in range(i + 1, len(instrs)):
            if j in starts or mnemonic(instrs[j - 1]) in BRANCHES:
                break
            regs = registers(instrs[j])
            if dst not in regs:
                continue
            if mnemonic(instrs[j]) == MIX[op] and regs[1:] == [dst]:
                pairs += 1
                if j != i + 1:
                    errors.append(
                        f"{name}:{lines[i]}: `{instr}` and its `{instrs[j]}` "
                        f"(line {lines[j]}) are not adjacent, so they do not fuse: "
                        f"`{instrs[i + 1]}` is between them"
                    )
            break
    return errors, pairs


def main():
    errors = []
    pairs = 0
    for path in sorted((ASM / TARGET).glob("*.rs")):
        text = path.read_text()
        offset = 0
        first_line = 1
        for m in FN.finditer(text):
            name, body = m.groups()
            first_line += text.count("\n", offset, m.start(2))
            offset = m.start(2)
            instrs, lines, labels = code(body, first_line)
            where = f"{path.relative_to(ROOT)} ({name})"
            errs, n = check_function(where, instrs, lines, labels)
            errors += errs
            pairs += n
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print(f"each of {pairs} AES round pairs (aese/aesmc, aesd/aesimc) is adjacent")
    return 0


if __name__ == "__main__":
    sys.exit(main())
