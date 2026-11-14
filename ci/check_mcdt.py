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
  slot the prologue's `stmxcsr` saved to. (That the value it loads is the
  caller's is proven: MXCSR's control bits are callee-saved in the
  contracts.)

A region is only entered through its prologue: no jump from outside it may
land inside it, and it may not contain a `ret`. So a cold branch
(`Code.iteCold`) may not start inside a region either: its code lies after
the function's `ret`, and its jump back would enter the region from outside.

A region may `call` an internal function that runs only inside regions
(`region_only`), so that one region can cover a computation's many calls of
its multiplications instead of each call setting MXCSR again. Such a
function:

* is internal (`assembly/internal/<name>.s`, `VG.Rust.Internal`): only the
  verified functions of its crate call it, as their code does (`Code.call`),
  never Rust code, so the `call`s of the assembly files are all its calls;
* has no instruction that reads or writes MXCSR, so MXCSR holds `0x1FBF`
  for all of it, as for the instructions of the region that called it;
* is called at least once, and each of its calls, in any function of its
  crate, is inside a region or in another such function. (Recursion is not
  needed and not accepted: the set is the least one closed under this.)

Its affected instructions then run inside the region of each call that
reaches them: after the prologue's `lfence` and before the epilogue's. A
`call` inside a region of any other function, or of no named function, is
rejected. The check is conservative: it rejects every affected instruction
outside a region and every such function, whether or not its operands are
secret.
"""

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
MXCSR_OPS = ("ldmxcsr", "stmxcsr")
CALL = re.compile(r"call \{(vg_\w+)\}")


def functions(text):
    """The functions of an assembly file, in order: each one's name, its
    instructions, the line of the file each is on, and where each numeric
    label is (the index of the instruction it precedes); and the lines that
    are none of these."""
    fns, unread = [], []
    for number, line in enumerate(text.split("\n"), 1):
        if m := FN.match(line):
            fns.append((m.group(1), [], [], {}))
        elif not line or line.startswith("//"):
            continue
        elif not fns:
            unread.append(number)
        elif line.startswith("\t"):
            fns[-1][1].append(line[1:])
            fns[-1][2].append(number)
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


def callee(instr):
    """The function a `call` names (`call {vg_f}`), or `None`."""
    m = CALL.fullmatch(instr)
    return m.group(1) if m else None


def find_regions(name, instrs, lines, labels):
    """The errors of the prologues and epilogues of a function, its regions
    (`(first, end)`: `instrs[first:end]` is protected), the region each
    instruction is in (or `None`), and each instruction's mnemonic."""
    errors = []

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
            regions.append((first, fence))
            i = end + 1
        else:
            i += 1

    # The region each instruction is in, if any.
    region_at = [None] * len(instrs)
    for r in regions:
        region_at[r[0] : r[1]] = [r] * (r[1] - r[0])
    return errors, regions, region_at, mnemonics


def check_function(name, instrs, lines, labels, inside=False, region_only=frozenset(), why=None,
                   found=None):
    """The errors of a function and its number of regions. `inside`: it runs
    only inside regions (`region_only`), the set of such functions of its
    crate; `why`: if it is not one but internal, why not; `found`: its
    `find_regions`, if already computed."""
    errors, regions, region_at, mnemonics = found or find_regions(name, instrs, lines, labels)
    errors = list(errors)

    def at(k):
        return f"{name}:{lines[k]}"

    for k, (instr, op) in enumerate(zip(instrs, mnemonics)):
        r = region_at[k]
        if op in AFFECTED and r is None and not inside:
            errors.append(
                f"{at(k)}: `{instr}` is outside Intel's MXCSR prologue and "
                "epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"
                + (f": its function is not called only inside MCDT regions ({why})" if why else "")
            )
        if op == "call" and r is not None:
            f = callee(instr)
            if f not in region_only:
                errors.append(
                    f"{at(k)}: `{instr}` is inside an MCDT region, and calls no internal "
                    "function that runs only inside MCDT regions"
                )
            continue
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


def region_only(fns):
    """Of the functions of a crate (`(where, name, instrs, lines, labels,
    internal, found)`, `found` their `find_regions`), the names of those that
    run only inside regions, and for each other internal function why it does
    not: the least set of internal functions with no MXCSR instruction,
    called at least once, each of whose calls is inside a region or in a
    function of the set."""
    calls = {}  # callee: [(caller, line, inside a region)]
    for where, name, instrs, lines, _, _, (_, _, region_at, mnemonics) in fns:
        for k, op in enumerate(mnemonics):
            if op == "call" and (f := callee(instrs[k])):
                calls.setdefault(f, []).append((name, f"{where}:{lines[k]}", region_at[k] is not None))
    candidates, why = set(), {}
    for _, name, instrs, _, _, internal, _ in fns:
        if not internal:
            continue
        if any(mnemonic(x) in MXCSR_OPS for x in instrs):
            why[name] = "it reads or writes MXCSR"
        elif name not in calls:
            why[name] = "it is never called"
        else:
            candidates.add(name)
    inside = set()
    while True:
        new = {f for f in candidates - inside
               if all(r or c in inside for c, _, r in calls[f])}
        if not new:
            break
        inside |= new
    for f in candidates - inside:
        c, line, _ = next(x for x in calls[f] if not (x[2] or x[0] in inside))
        why[f] = f"{c} calls it outside an MCDT region, at {line}"
    return frozenset(inside), why


def main():
    errors = []
    regions = 0
    for target_name in TARGETS:
        src = asm_layout.target_dir(ROOT, target_name)
        fns = []
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
            read, unread = functions(assembly.read_text())
            where = assembly.relative_to(ROOT)
            errors += [f"{where}:{n}: neither a function, an instruction nor a label" for n in unread]
            internal = path.parent.name == "internal"
            fns += [(where, *fn, internal, find_regions(f"{where} ({fn[0]})", *fn[1:])) for fn in read]
            if len(read) != naked:
                errors.append(f"{where}: lists {len(read)} of the {naked} naked functions of "
                              f"{path.relative_to(ROOT)}")
        # The call graph is by name: each function's must be its own.
        seen = {}
        for where, name, *_ in fns:
            if name in seen:
                errors.append(f"{where}: defines {name}, as {seen[name]} does")
            seen.setdefault(name, where)
        inside, why = region_only(fns)
        for where, name, instrs, lines, labels, _, found in fns:
            errs, n = check_function(f"{where} ({name})", instrs, lines, labels,
                                     name in inside, inside, why.get(name), found)
            errors += errs
            regions += n
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print(f"every MCDT-affected instruction is inside one of {regions} MXCSR-protected regions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
