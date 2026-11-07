#!/usr/bin/env python3
"""Checks that the generated x86 code never pays an SSE/AVX transition,
from the assembly files of the generated code of
`crates/verified-garbage-asm-x86_64/` and `crates/verified-garbage-asm-x86/`
(`assembly/<module>.s` and `assembly/internal/<name>.s`, the text of the
machine code of `src/`; see `check_mcdt.py`).

A VEX- or EVEX-encoded instruction that writes a `ymm` or `zmm` register
leaves the upper bits of the vector registers *dirty* until `vzeroupper` or
`vzeroall`. A legacy-SSE instruction (one without a VEX or EVEX prefix) that
writes an `xmm` register while they are dirty must preserve those upper
bits, and pays a state transition (or a merge with the upper bits) for it
(Intel, Optimization Reference Manual, "Mixing AVX code with SSE code"). On
a Sapphire Rapids-class Xeon, a loop of AVX-512 code with two legacy moves
into `xmm` registers took about 300 cycles an iteration, against 1.3 with
EVEX moves in their place; a legacy `pxor` after a `ymm` or `zmm` write about
220 cycles. Code returning with dirty upper state taxes its caller's SSE code
(Rust's baseline x86-64 code is SSE) the same way. So in each function,
entered with clean upper state as the ABI expects:

* no legacy-SSE instruction writes an `xmm` register while the upper state
  may be dirty;
* no `ret` is reached, and no indirect `call` (of code this check cannot
  see) made, while it may be dirty;
* a direct `call` of another generated function is checked with that
  function's own code: from the state at the call, the callee may not write
  an `xmm` register with legacy SSE while dirty, and the caller continues in
  the state the callee's `ret`s may leave.

The check follows each function's control flow (its jumps to numeric local
labels, `Nf` and `Nb`, and its code after a `ret`, reached only by jumps)
and the calls between functions, and computes, at each instruction, whether
the upper state may be dirty there on some path: it is conservative,
assuming every branch can go either way.

An instruction is VEX- or EVEX-encoded exactly when its Intel-syntax
mnemonic starts with `v` (every AVX and AVX-512 form of an SSE instruction
is its `v`-prefixed name, and no legacy-SSE mnemonic starts with `v`); the
opmask (`k*`) and BMI instructions, which have no `v`, name no `xmm`
register, and are not SSE. It writes a `ymm`/`zmm` register when its first
operand (its destination, in Intel syntax) is one of `ymm0`–`ymm15` or
`zmm0`–`zmm15`: `zmm16`–`zmm31` have no legacy-SSE alias, are not cleared by
`vzeroupper`, and so never make the upper state dirty (which is why AVX-512
code can use them to avoid `vzeroupper`). A legacy-SSE instruction writes an
`xmm` register when its first operand is one (which counts `ptest` and the
comparisons that only set flags too, conservatively), or it is one of
`IMPLICIT_XMM0`, which write `xmm0`. A legacy-SSE instruction that only
reads `xmm` registers (a store, `movq r64, xmm`, `pextrq`) has nothing to
merge and is not counted: on the same Xeon it ran at full speed with the
upper state dirty, as `ldmxcsr` and `stmxcsr` did.
"""

import pathlib
import re
import sys

import asm_layout
from check_mcdt import functions, mnemonic, operands, target

ROOT = pathlib.Path(__file__).resolve().parent.parent
TARGETS = ("x86", "x86_64")

XMM = re.compile(r"xmm\d+")
# The registers whose upper bits `vzeroupper` clears.
WIDE = re.compile(r"^[yz]mm([0-9]|1[0-5])$")
CLEAN = {"vzeroupper", "vzeroall"}
CALLEE = re.compile(r"^\{(vg_\w+)\}$")


# Legacy-SSE instructions that write `xmm0` without naming it (SDM Vol. 2,
# "PCMPESTRM", "PCMPISTRM": the mask is written to XMM0).
IMPLICIT_XMM0 = {"pcmpestrm", "pcmpistrm"}


def writes_xmm_legacy(instr):
    """Whether `instr` is a legacy-SSE (non-VEX, non-EVEX) instruction that
    writes an `xmm` register."""
    op = mnemonic(instr)
    if op.startswith("v") or op.startswith("."):
        return False
    ops = operands(instr)
    return op in IMPLICIT_XMM0 or (bool(ops) and XMM.fullmatch(ops[0]) is not None)


def writes_wide(instr):
    """Whether `instr` writes one of `ymm0`–`ymm15` or `zmm0`–`zmm15`."""
    ops = operands(instr)
    return mnemonic(instr).startswith("v") and bool(ops) and WIDE.match(ops[0]) is not None


class Program:
    """Every generated function of a target, by name, each with the file it
    is in: `(where, instrs, lines, labels)` as `check_mcdt.functions` reads
    them."""

    def __init__(self, fns):
        self.fns = fns
        # (name, entry dirty) → (errors, set of dirty states at its `ret`s)
        self.summaries = {}
        self.active = set()

    def summary(self, name, dirty):
        key = (name, dirty)
        if key in self.summaries:
            return self.summaries[key]
        self.active.add(key)
        result = self.analyse(name, dirty)
        self.active.discard(key)
        self.summaries[key] = result
        return result

    def analyse(self, name, entry):
        """`name`'s errors when entered with upper state `entry` (dirty or
        not), and the states its `ret`s may leave. A `ret` with dirty upper
        state is an error only when it was entered clean: otherwise the
        caller made the state dirty, and is checked for it."""
        where, instrs, lines, labels = self.fns[name]
        errors = []
        exits = set()
        n = len(instrs)
        states = [set() for _ in range(n)]
        reported = set()

        def at(k):
            return f"{where}:{lines[k]} ({name})"

        def error(k, msg):
            if (k, msg) not in reported:
                reported.add((k, msg))
                errors.append(f"{at(k)}: `{instrs[k]}` {msg}")

        work = []

        def flow(k, dirty, src):
            if k >= n:
                error(src, "falls through past the end of its function")
                return
            if dirty not in states[k]:
                states[k].add(dirty)
                work.append((k, dirty))

        if n:
            flow(0, entry, 0)
        while work:
            k, dirty = work.pop()
            instr = instrs[k]
            op = mnemonic(instr)
            if op in CLEAN:
                flow(k + 1, False, k)
            elif op == "ret":
                if dirty and not entry:
                    error(k, "returns with dirty upper state (no vzeroupper since a ymm/zmm write)")
                exits.add(dirty)
            elif op == "call":
                ops = operands(instr)
                m = CALLEE.match(ops[0]) if len(ops) == 1 else None
                if m and (m.group(1), dirty) in self.active:
                    # Recursion: never generated, and not handled.
                    error(k, "is a recursive call, which this check does not handle")
                    flow(k + 1, True, k)
                elif m and m.group(1) in self.fns:
                    callee = m.group(1)
                    errs, outs = self.summary(callee, dirty)
                    # A callee's errors from clean entry are reported for
                    # the callee itself.
                    if errs and dirty:
                        error(k, f"calls {callee} with dirty upper state, which then: " + "; ".join(errs))
                    for out in outs:
                        flow(k + 1, out, k)
                else:
                    if dirty:
                        error(k, "calls code this check cannot see with dirty upper state")
                    flow(k + 1, False, k)
            elif op.startswith("j"):
                t = target(instr, k, labels)
                if t is None:
                    error(k, "jumps to a target this check cannot resolve")
                else:
                    flow(t, dirty, k)
                if op != "jmp":
                    flow(k + 1, dirty, k)
            else:
                if dirty and writes_xmm_legacy(instr):
                    error(k, "writes an xmm register with legacy SSE after a ymm/zmm write "
                          "with no vzeroupper between them")
                flow(k + 1, dirty or writes_wide(instr), k)
        return errors, exits


def main():
    errors = []
    checked = 0
    for target_name in TARGETS:
        src = asm_layout.target_dir(ROOT, target_name)
        assembly = src.parent / "assembly"
        fns = {}
        for path in sorted(assembly.glob("*.s")) + sorted(assembly.glob("internal/*.s")):
            where = path.relative_to(ROOT)
            found, unread = functions(path.read_text())
            errors += [f"{where}:{n}: neither a function, an instruction nor a label" for n in unread]
            for name, instrs, lines, labels in found:
                if name in fns:
                    errors.append(f"{where}: {name} is also in {fns[name][0]}")
                fns[name] = (where, instrs, lines, labels)
        program = Program(fns)
        for name in fns:
            errs, _ = program.summary(name, False)
            errors += errs
            checked += 1
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print(f"none of {checked} functions writes an xmm register with legacy SSE, "
          "returns or calls out with dirty ymm/zmm upper state")
    return 0


if __name__ == "__main__":
    sys.exit(main())
