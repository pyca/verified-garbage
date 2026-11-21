#!/usr/bin/env python3
"""Checks that the generated x86 code only runs the instructions affected by
MXCSR-configuration-dependent timing (MCDT) under Intel's mitigation, from
the assembly files of the generated code of `crates/verified-garbage-asm-x86_64/`
and `crates/verified-garbage-asm-x86/`, `assembly/<module>.s`: the text of
each instruction of `src/<module>.rs`, whose machine code that file holds
(the emitter writes both from the same printed code, `TCB/Rust.lean`), and
`assembly/internal/<name>.s`, of each internal function's
`src/internal/<name>.rs`.

On some Intel processors, a few vector multiplies (Intel's list, "MCDT Data
Operand Independent Timing Instructions": `pmuludq`, `pmullw`, `pmulhw`,
`pmaddwd`, `pmulhrsw`, their VEX/EVEX forms, and others the ISA models do
not have yet) may take a cycle longer for specific data values unless MXCSR
holds `0x1FBF`. The leakage model of the proofs does not see this (see "MCDT" in
`lean/VerifiedGarbage/TCB/X86_64/Isa.lean`), so this script checks that each
such instruction is inside a *protected region* of its function, which is
Intel's sequence, exactly:

* the prologue: `stmxcsr` (saving the caller's MXCSR), then, in the same
  straight-line code, `mov r32, 8127` (`0x1FBF`), `mov DWORD PTR [m], r32`,
  `ldmxcsr DWORD PTR [m]` and `lfence`, one after the other;
* the region: the code after that `lfence`, up to the next instruction that
  reads or writes MXCSR, which must be the epilogue's `ldmxcsr`;
* the epilogue: `lfence`, then straight-line `mov`s, then `ldmxcsr` of the
  slot the prologue's `stmxcsr` saved to.
  The value it loads keeps the status flags it was saved with, or has them
  set (`flags_kept`): code after it may rely on flags set before it. (That the value it loads is the
  caller's is proven: MXCSR's control bits are callee-saved in the
  contracts.)

One function loads MXCSR otherwise: `vg_mcdt_enter`, of the module `mcdt`
of x86-64, which sets its status flags (`lean/VerifiedGarbage/Spec/Mcdt.lean`).
It may neither run an instruction on Intel's list nor call.

On x86-64, an affected instruction may also be outside any region, in a
function every run of which is under `vg_mcdt_enter` (`entered`), which
leaves MXCSR `0x1FBF` until the function returns (the regions inside
restore what they found). The generated dispatchers run it first for every
function whose code has such an instruction (`lean/VerifiedGarbage/TCB/Rust.lean`,
"Dispatchers"), and Rust reaches the verified functions only through them:
so such a function is `pub(crate)`, the crate's Rust names it only in
dispatchers whose first line runs `vg_mcdt_enter`, never in a table of
functions, and every function that calls it is one too, or calls it after
its own call of `vg_mcdt_enter` returned 1 (below).

On x86-64, the verified code may also call `vg_mcdt_enter` itself, only on
the paths that reach affected instructions, so that the others (short
inputs) do not pay for it (`Rust.mcdtOpen`, whose dispatchers then do not
run it): an affected instruction may be outside any region where every path
to it from its function's entry passes `call {vg_mcdt_enter}`, `test eax,
eax` and the fall-through of a `je` (taken when it returned 0), neither of
the last two labelled (`guarded`); and so may a function every call of which
is on such a path, or from a function that is `entered`. `vg_mcdt_enter`
returns 1 only with MXCSR `0x1FBF` (`VG.Proof.Mcdt.X86_64.enter_mxcsr`),
which it keeps until the function returns, as above.

A region is only entered through its prologue: no jump from outside it may
land inside it, and it may not contain a `call` or `ret`. So a cold branch
(`Code.iteCold`) may not start inside a region either: its code lies after
the function's `ret`, and its jump back would enter the region from outside. The check is
conservative: it rejects every affected instruction outside a region,
whether or not its operands are secret.
"""

import bisect
import pathlib
import re
import sys

import asm_layout

ROOT = pathlib.Path(__file__).resolve().parent.parent
TARGETS = ("x86", "x86_64")

# Intel, "MCDT Data Operand Independent Timing Instructions", Table 1.
AFFECTED = {
    "pmaddubsw", "pmaddwd", "pmuldq", "pmulhrsw", "pmulhuw", "pmulhw",
    "pmulld", "pmullw", "pmuludq",
    "vplzcntd", "vplzcntq", "vpmadd52huq", "vpmadd52luq", "vpmaddubsw",
    "vpmaddwd", "vpmuldq", "vpmulhrsw", "vpmulhuw", "vpmulhw", "vpmulld",
    "vpmullq", "vpmullw", "vpmuludq",
}  # fmt: skip

# A function of an assembly file (`Rust.moduleAssembly`): its name, then its lines,
# each instruction indented by a tab, each label not.
FN = re.compile(r"^(vg_\w+):$")
LABEL = re.compile(r"^(\d+):$")
MXCSR_VALUE = {"8127", "0x1FBF", "0x1fbf"}
# `vg_mcdt_enter` (`lean/VerifiedGarbage/Impl/Mcdt/X86_64.lean`), the one
# function that loads MXCSR other than in Intel's prologue and epilogue: of
# the module `mcdt` of the target `x86_64`.
ENTER = ("x86_64", "mcdt.s", "vg_mcdt_enter")


def functions(text):
    """The functions of an assembly file, in order: each one's name, its
    instructions, the line of the file each is on, and where each numeric
    label is (the index of the instruction it precedes); and the lines that
    are none of these."""
    fns, unread = [], []
    instrs = numbers = None
    for number, line in enumerate(text.split("\n"), 1):
        # Instructions first, nearly every line: neither `FN` nor a comment
        # starts with a tab.
        if line.startswith("\t"):
            if fns:
                instrs.append(line[1:])
                numbers.append(number)
            else:
                unread.append(number)
        elif m := FN.match(line):
            fns.append((m.group(1), [], [], {}))
            instrs, numbers = fns[-1][1], fns[-1][2]
        elif not line or line.startswith("//"):
            continue
        elif not fns:
            unread.append(number)
        elif m := LABEL.match(line):
            fns[-1][3].setdefault(m.group(1), []).append(len(fns[-1][1]))
        else:
            unread.append(number)
    return fns, unread


def mnemonic(instr):
    return instr.split(None, 1)[0]


def operands(instr):
    parts = instr.split(None, 1)
    return [o.strip() for o in parts[1].split(",")] if len(parts) > 1 else []


def is_branch(instr):
    return mnemonic(instr).startswith("j") or mnemonic(instr) in ("call", "ret")


def target(instr, i, labels):
    """The index a jump at `i` lands on, or `None` if it is not a jump to a
    numeric local label."""
    ops = operands(instr)
    m = re.fullmatch(r"(\d+)([fb])", ops[0]) if len(ops) == 1 else None
    if not m or m.group(1) not in labels:
        return None
    defs = labels[m.group(1)]
    if m.group(2) == "b":
        before = [d for d in defs if d <= i]
        return before[-1] if before else None
    after = [d for d in defs if d > i]
    return after[0] if after else None


def straight(instrs, lo, hi, labels):
    """Whether `instrs[lo:hi]` is straight-line code: no branch in it, and
    no label inside it."""
    inside = any(lo < d < hi for defs in labels.values() for d in defs)
    return not inside and not any(is_branch(x) for x in instrs[lo:hi])


def prologue(instrs, i, labels):
    """If `instrs[i]` is the `ldmxcsr` of Intel's prologue, the memory
    operand its `stmxcsr` saved MXCSR to; otherwise an error."""
    if i < 3 or i + 1 >= len(instrs) or instrs[i + 1] != "lfence":
        return None, "not followed by lfence"
    (slot,) = operands(instrs[i])
    load, store = instrs[i - 2], instrs[i - 1]
    lops, sops = operands(load), operands(store)
    if not (
        mnemonic(load) == "mov"
        and len(lops) == 2
        and lops[1] in MXCSR_VALUE
        and mnemonic(store) == "mov"
        and sops == [slot, lops[0]]
    ):
        return None, "not preceded by `mov r32, 8127` and a store of it to its operand"
    for j in range(i - 3, -1, -1):
        if mnemonic(instrs[j]) == "stmxcsr":
            if not straight(instrs, j, i + 2, labels):
                break
            return operands(instrs[j])[0], None
    return None, "not preceded by stmxcsr in the same straight-line code"


def flags_kept(instrs, i, fence, end, saved):
    """Whether the epilogue ending at `instrs[end]` restores a value of MXCSR
    with the status flags it was saved with, or with them set: never one with
    them cleared, so that code after it may rely on flags that code before it
    set (Intel's mitigation is MXCSR `0x1FBF`, the default control bits with
    every flag set). It follows the saved value, in the prologue (from its
    `stmxcsr` to its `ldmxcsr` at `i`) and the epilogue's movs: loaded from
    the slot into a register, `and` with an immediate that keeps bits 5:0 or
    `or` with one that sets them, and stored back."""
    j = i - 1
    while mnemonic(instrs[j]) != "stmxcsr":
        j -= 1
    regs, slot = {}, "saved"

    def imm(x):
        try:
            return int(x, 0)
        except ValueError:
            return None

    def step(x):
        nonlocal slot
        op, ops = mnemonic(x), operands(x)
        if op == "mov" and len(ops) == 2 and ops[1] == saved:
            regs[ops[0]] = slot
        elif op == "mov" and len(ops) == 2 and ops[0] == saved:
            slot = regs.get(ops[1], "unknown")
        elif op in ("and", "or") and len(ops) == 2 and ops[0] in regs and imm(ops[1]) is not None:
            kept = imm(ops[1]) & 63 == 63
            if op == "and" and not kept:
                regs[ops[0]] = "cleared"
            elif op == "or" and kept:
                regs[ops[0]] = "set"
        elif ops:
            regs.pop(ops[0], None)

    for x in instrs[j + 1:i] + instrs[fence + 1:end]:
        step(x)
    return slot in ("saved", "set")


# The test of `vg_mcdt_enter`'s result after a call of it (`Rust.mcdtOpen`), and
# the branches taken when it returned 0.
GUARD_TEST = "test eax, eax"
GUARD_JUMPS = ("je", "jz")


def guarded(instrs, labels):
    """For each instruction of a function, whether every path to it from the
    function's entry passes a call of `vg_mcdt_enter` that returned 1 (the
    code `Rust.mcdtOpen` lets run without the dispatcher's): it falls through
    a `je` (taken when `eax` is 0) right after `test eax, eax` right after
    `call {vg_mcdt_enter}`, with no label on the test or the `je`, which
    nothing but that call then reaches. MXCSR then holds `0x1FBF` until the
    function returns (`vg_mcdt_enter` returns 1 only then, and the regions
    restore the value they saved, with its flags). All `False` if the target
    of a jump is unknown. Paths follow the fall-through of every instruction
    but `jmp` and `ret`, a call returning to the next, and the target of each
    jump; an instruction no path reaches is `True`."""
    n = len(instrs)
    labelled = {d for defs in labels.values() for d in defs}
    enter = f"call {{{ENTER[2]}}}"
    # An instruction is `False` exactly when a path from the entry reaches it
    # without passing a guard: the greatest solution of "`True` but at the
    # entry, and where every predecessor is `True` or reaches it through a
    # guard". Find those paths forward from the entry, each instruction once.
    # Only branches end a run of fall-throughs: the others are skipped by
    # their first character, which is their mnemonic's.
    jumps = {}  # index of each branch: (its target or None, whether it falls through)
    for k, x in enumerate(instrs):
        if not x.startswith(("j", "r")) and not x[:1].isspace():
            continue
        op = mnemonic(x)
        if op == "ret":
            jumps[k] = (None, False)
        elif op.startswith("j"):
            t = target(x, k, labels)
            if t is None:
                return [False] * n
            jumps[k] = (t if t < n else None, op != "jmp")
            if (op in GUARD_JUMPS and k >= 2 and instrs[k - 1] == GUARD_TEST and
                    instrs[k - 2] == enter and k - 1 not in labelled and k not in labelled):
                jumps[k] = (jumps[k][0], False)
    stops = sorted(jumps)
    reached = bytearray(n)
    work = [0] if n else []
    while work:
        k = work.pop()
        if reached[k]:
            continue
        # The run from `k` to the next branch, inclusive, is reached.
        i = bisect.bisect_left(stops, k)
        end = stops[i] if i < len(stops) else n - 1
        j = k
        while j <= end and not reached[j]:
            reached[j] = 1
            j += 1
        if j <= end:
            continue  # the rest of the run was already reached, from its start
        if end in jumps:
            t, falls = jumps[end]
            if t is not None:
                work.append(t)
            if falls and end + 1 < n:
                work.append(end + 1)
    return [not r for r in reached]


def check_function(name, instrs, lines, labels, entered=False, guard=None):
    """The errors of a function and its number of regions. `entered`: every
    run of it is under `vg_mcdt_enter` (`entered`), so its affected
    instructions need no region; `guard`: which of its instructions run only
    after its own call of `vg_mcdt_enter` returned 1 (`guarded`), which need
    none either."""
    errors = []
    guard = guard or [False] * len(instrs)

    def at(k):
        return f"{name}:{lines[k]}"

    # Each instruction's mnemonic, computed once: functions have up to
    # hundreds of thousands of instructions.
    mnemonics = [mnemonic(x) for x in instrs]
    regions = []  # (first, end): instrs[first:end] is protected
    i = 0
    while i < len(instrs):
        if mnemonics[i] == "ldmxcsr":
            saved, why = prologue(instrs, i, labels)
            if why:
                errors.append(f"{at(i)}: `{instrs[i]}` is not Intel's MCDT prologue: {why}")
                i += 1
                continue
            first = i + 2
            end = first
            while end < len(instrs) and mnemonics[end] not in ("ldmxcsr", "stmxcsr"):
                end += 1
            if end == len(instrs) or mnemonics[end] != "ldmxcsr":
                errors.append(
                    f"{at(first - 1)}: the MCDT region after this prologue has no epilogue"
                )
                break
            fence = end - 1
            while fence >= first and mnemonics[fence] == "mov":
                fence -= 1
            if (
                fence < first
                or instrs[fence] != "lfence"
                or not straight(instrs, fence, end + 1, labels)
                or operands(instrs[end]) != [saved]
            ):
                errors.append(
                    f"{at(end)}: `{instrs[end]}` is not Intel's MCDT epilogue: "
                    f"lfence, then straight-line movs, then ldmxcsr of {saved}"
                )
            elif not flags_kept(instrs, i, fence, end, saved):
                errors.append(
                    f"{at(end)}: `{instrs[end]}` may restore MXCSR with its status flags "
                    "cleared, which code after it may rely on"
                )
            regions.append((first, fence))
            i = end + 1
        else:
            i += 1

    # The region each instruction is in, if any.
    region_at = [None] * len(instrs)
    for r in regions:
        region_at[r[0] : r[1]] = [r] * (r[1] - r[0])
    for k, (instr, op) in enumerate(zip(instrs, mnemonics)):
        r = region_at[k]
        if op in AFFECTED and r is None and not entered and not guard[k]:
            errors.append(
                f"{at(k)}: `{instr}` is outside Intel's MXCSR prologue and "
                "epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"
            )
        if op in ("call", "ret"):
            if r is not None:
                errors.append(f"{at(k)}: `{instr}` is inside an MCDT region")
            continue
        if op.startswith("j"):
            t = target(instr, k, labels)
            if t is None:
                if regions:
                    errors.append(f"{at(k)}: cannot resolve the target of `{instr}`")
                continue
            # Entering a region other than through its prologue; the
            # region's first instruction is entered by the prologue's
            # fall-through, or by a jump from inside the region (a loop).
            rt = region_at[t]
            if rt is not None and rt != r:
                errors.append(
                    f"{at(k)}: `{instr}` jumps into the MCDT region at "
                    f"line {lines[rt[0]]} from outside it"
                )
    return errors, len(regions)


CALL = re.compile(r"call \{(vg_\w+)\}")
# A dispatcher (`Rust.dispatcher`): its signature's line, and the lines of its
# body up to the `}` closing it.
DISPATCHER = re.compile(r"^pub unsafe fn (vg_\w+_auto)\(.*\n((?:(?!\}\n).*\n)*?)\}$", re.M)
# The lines with which a dispatcher runs `vg_mcdt_enter` first (`Rust.mcdtLine`).
ENTER_LINE = ("    // SAFETY: it takes no argument and writes no memory but its stack.\n"
              "    verified_garbage_cpu::mcdt_entered(unsafe { crate::mcdt::vg_mcdt_enter() });")
# The verified functions a piece of Rust names: `crate::<module>::<name>`.
NAMED = re.compile(r"\bcrate::(?:\w+::)*(vg_\w+)\b")
# A naked function visible outside its crate.
PUBLIC = re.compile(r"^pub unsafe extern \"[\w-]+\" fn (vg_\w+)", re.M)


def entered(fns, crate):
    """Of the functions `fns` of a target (each name with its instructions and
    labels), the names of those that only run under `vg_mcdt_enter`: no Rust
    outside the crate `crate` may name it (it is `pub(crate)`); the crate's
    Rust names it only in dispatchers that run `vg_mcdt_enter` first
    (`ENTER_LINE`, their first lines), never in a table of functions, and
    names it there or calls it from another function; and every call of it is
    from a function that is one too, or after that function's own call of
    `vg_mcdt_enter` returned 1 (`guarded`). (The functions of the crate's
    modules name the functions they call only as the `sym` operands of those
    calls, which are the `call`s of their assembly.)"""
    src = crate / "src"
    public = {f for path in src.glob("*.rs") for f in PUBLIC.findall(path.read_text())}
    direct, wrapped = set(), set()
    for path in sorted((src / "dispatch").glob("*.rs")):
        for _, body in DISPATCHER.findall(path.read_text()):
            names = set(NAMED.findall(body))
            if body.startswith(ENTER_LINE + "\n"):
                wrapped |= names
            else:
                direct |= names
    for path in sorted((src / "fn_tables").glob("*.rs")):
        direct |= set(NAMED.findall(path.read_text()))
    callers = {}  # callee: {(caller, whether the call is guarded)}
    for name, instrs, labels in fns:
        guard = None
        for k, x in enumerate(instrs):
            if x.startswith("call") and (m := CALL.fullmatch(x)):
                if guard is None:
                    guard = guarded(instrs, labels)
                callers.setdefault(m.group(1), set()).add((name, guard[k]))
    out = {}

    def ok(f, seen):
        if f not in out:
            out[f] = (f not in public and f not in direct and f != ENTER[2] and
                      (f in wrapped or f in callers) and
                      all(g or (c not in seen and ok(c, seen | {c})) for c, g in callers.get(f, ())))
        return out[f]

    return {name for name, _, _ in fns if ok(name, {name})}


def check_enter(name, instrs, lines):
    """The errors of `vg_mcdt_enter`, which sets MXCSR's status flags (what
    it leaves in MXCSR is proven: `VG.Proof.Mcdt.X86_64.enter_mxcsr`): it may
    load MXCSR as it does, as no prologue does, but runs no instruction
    that MCDT affects, and calls nothing."""
    return [f"{name}:{lines[k]}: `{x}` is in vg_mcdt_enter, which may neither run an instruction "
            "MCDT affects nor call"
            for k, x in enumerate(instrs) if mnemonic(x) in AFFECTED or mnemonic(x) == "call"]


def main():
    errors = []
    regions = 0
    for target_name in TARGETS:
        src = asm_layout.target_dir(ROOT, target_name)
        read = []
        for path in sorted(src.glob("*.rs")) + sorted(src.glob("internal/vg_*.rs")):
            # Every naked function is checked: each is in its module's assembly file
            # (an internal function's, `internal/<name>.rs`, in `internal/<name>.s`),
            # which must be read in full, and this not pass on a function left
            # unread.
            naked = path.read_text().count("#[unsafe(naked)]")
            assembly = (src.parent / "assembly" / path.relative_to(src)).with_suffix(".s")
            if not assembly.is_file():
                if naked:
                    errors.append(f"{path.relative_to(ROOT)}: has no assembly file {assembly.relative_to(ROOT)}")
                continue
            fns, unread = functions(assembly.read_text())
            where = assembly.relative_to(ROOT)
            errors += [f"{where}:{n}: neither a function, an instruction nor a label" for n in unread]
            read += [(where, assembly.name, fn) for fn in fns]
            if len(fns) != naked:
                errors.append(f"{where}: lists {len(fns)} of the {naked} naked functions of "
                              f"{path.relative_to(ROOT)}")
        # Only x86-64 has `vg_mcdt_enter`, which its dispatchers run.
        x86_64 = target_name == ENTER[0]
        under = entered([(fn[0], fn[1], fn[3]) for _, _, fn in read], src.parent) if x86_64 else set()
        for where, file, (name, instrs, lines, labels) in read:
            if (target_name, file, name) == ENTER:
                errors += check_enter(f"{where} ({name})", instrs, lines)
                continue
            guard = guarded(instrs, labels) if x86_64 and f"call {{{ENTER[2]}}}" in instrs else None
            errs, n = check_function(f"{where} ({name})", instrs, lines, labels, name in under, guard)
            errors += errs
            regions += n
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print(f"every MCDT-affected instruction is inside one of {regions} MXCSR-protected regions, "
          "or runs under vg_mcdt_enter")
    return 0


if __name__ == "__main__":
    sys.exit(main())
