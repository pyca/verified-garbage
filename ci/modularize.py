#!/usr/bin/env python3
"""Converts Lean files to modules of Lean's module system, keeping what
every importer sees. It was used to convert the library, a layer at a time;
it is kept for the one-off pass that makes imports private, and goes after
it. New files are written as modules by hand (CLAUDE.md, "Lean modules"),
and `ci/check_lean_modules.py` checks that they are.

  modularize.py PATH...   convert each `.lean` file at PATH (a file or a
                          directory, recursively) that is not a module yet

A converted file starts with `module`; its imports become `public import`;
and its body is an `@[expose] public section`, so that every declaration
stays visible to importers with its definition, as before.

A file that only defines tactics, elaborators or commands (it declares
`elab`, `syntax`, `macro` or `simproc`s, and no theorem, nor a command that
adds one, nor a structure, inductive type or instance unless it imports
`Lean`) is meta code: its
body is a `public meta section`, so that its definitions run at elaboration
time in the files that use them, and each of its imports is also a
`public meta import` (only that, for `Lean`'s), so that its code can run
theirs. A file that declares such meta code next to definitions or theorems
(marking `meta` the definitions its tactics run) imports `Lean` both ways:
`public import` and `public meta import`.

A file that evaluates code while it is elaborated (`#guard`, `#eval`,
`run_cmd`, ..., and the framework's `materialize_*` and `taint_decide`/
`taint_summary`, which run code to build literals and hints) also imports each of its imports as `meta import`, so that
what it evaluates is available to the compiler at that time.

A proof module (under `Proof/`, but not the framework) also imports the core
modules of `CORE_ALL` with `import all`, and those of `CORE_ALL_FOR` whose
definition it mentions.

A leading comment (a copyright notice) stays before `module`.
"""

import pathlib
import re
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

IMPORT = re.compile(r"^import\s+(\S+)\s*$")
META_DECL = re.compile(r"^(elab|syntax|macro|macro_rules|simproc|dsimproc|elab_rules)\b", re.M)
THEOREM = re.compile(r"^(@\[[^\]]*\]\s*)?(private\s+)?(theorem|lemma)\b", re.M)
META_MARK = re.compile(r"^\s*(@\[[^\]]*\]\s*)?((public|private|protected)\s+)?meta\s+(def|instance|section|abbrev|structure)\b", re.M)
EVAL_CMD = re.compile(r"^\s*(#guard|#eval|#reduce|run_cmd|run_elab|run_meta|materialize_\w+)\b", re.M)
EVAL_NAMES = ["taint_decide", "taint_summar"]


def evaluates(text: str, names: list[str]) -> bool:
    """Whether `text` runs code while it is elaborated: an evaluating command,
    a tactic or command whose name contains one of `EVAL_NAMES`, or one of the
    other `names` (not in a docstring's backquotes, a string, or a syntax
    quotation)."""
    if EVAL_CMD.search(text):
        return True
    pre = r"(^|[\s;·>]|(?<!`)\()"
    base = "|".join(re.escape(n) for n in EVAL_NAMES)
    if re.search(pre + r"\w*(" + base + r")\w*\b", text, re.M):
        return True
    others = [n for n in names if n not in EVAL_NAMES]
    return bool(others) and re.search(pre + r"(" + "|".join(map(re.escape, others)) + r")\b(?!`)",
                                      text, re.M) is not None


# A tactic or command defined by `macro "name" … => body` or `elab "name" …`,
# or by `macro_rules`/`elab_rules` on `(tactic| name …)`: its name and body.
DEFINES = re.compile(r'^(?:macro|elab)\b[^"\n]*"(\w+)|^(?:macro_rules|elab_rules)\b', re.M)
QUOTED = re.compile(r"`\((?:tactic|command)\|\s*(\w+)")


def blocks(text: str):
    """The top-level `macro`/`elab`/`…_rules` blocks of `text`: (names, body)."""
    starts = [m for m in DEFINES.finditer(text)]
    for k, m in enumerate(starts):
        end = text.find("\n\n", m.end())
        body = text[m.start():end if end >= 0 else len(text)]
        names = [m.group(1)] if m.group(1) else [q for q in QUOTED.findall(body.split("=>")[0])]
        yield names, body.split("=>", 1)[1] if "=>" in body else body


def evaluating_names(lean: pathlib.Path) -> list[str]:
    """`EVAL_NAMES`, and the project's tactics and commands whose definition
    runs one of them or evaluates a term itself (`evalExpr`), to a fixpoint:
    e.g. `kem_wf`, a macro for `taint_decide`, and `def_literal`."""
    bs = [b for f in (lean / "VerifiedGarbage" / "Proof").rglob("*.lean") for b in blocks(f.read_text())]
    names = list(EVAL_NAMES)
    while True:
        new = {n for ns, body in bs if evaluates(body, names) or "evalExpr" in body for n in ns if n not in names}
        if not new:
            return names
        names += sorted(new)


def is_module(lines: list[str]) -> bool:
    comment = False
    for l in lines:
        s = l.strip()
        if comment:
            comment = not s.endswith("-/")
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
            continue
        if s == "module":
            return True
        if s and not s.startswith("--"):
            return False
    return False


# Lean core modules with definitions the proofs evaluate (with `decide`,
# `rfl` or the kernel, e.g. Spec tables built with `Array.ofFn`) but that core
# does not expose to modules. A proof module imports them with `import all`,
# so that it sees their bodies as a non-module file does.
CORE_ALL = ["Init.Data.Array.Basic", "Init.Data.Array.DecidableEq", "Init.Data.Nat.Bitwise.Basic",
            "Init.Data.Vector.Basic"]
# Core modules a proof module imports with `import all` only if it mentions
# their definition: `Nat.isPowerOfTwo`, which core states as `∃ k, n = 2 ^ k`
# but neither exposes nor gives a lemma to take apart.
CORE_ALL_FOR = {"Init.Data.Nat.Power2.Basic": "isPowerOfTwo"}

# Commands that add theorems (and definitions) to the file that runs them.
PROOF_CMD = re.compile(r"^(materialize_\w+|taint_summary)\b", re.M)


# Declarations of data (not `meta`): a file with one is meta code only if
# it imports `Lean` (a tactic's own state, as in `Framework/SigEval.lean`).
DATA = re.compile(r"^(@\[[^\]]*\]\s*)?((private|protected)\s+)?(structure|inductive|class|instance)\b", re.M)


def is_meta(text: str, imports: list[str]) -> bool:
    uses_lean = any(i == "Lean" or i.startswith("Lean.") for i in imports)
    return (META_DECL.search(text) is not None and THEOREM.search(text) is None
            and PROOF_CMD.search(text) is None and (uses_lean or DATA.search(text) is None))


def is_proof(path: str) -> bool:
    p = pathlib.PurePosixPath(path).as_posix()
    return "VerifiedGarbage/Proof/" in p and "VerifiedGarbage/Proof/Framework/" not in p


def convert(text: str, proof: bool = False, names: list[str] = EVAL_NAMES) -> str:
    lines = text.split("\n")
    if is_module(lines):
        return text
    i, n, lead = 0, len(lines), []
    # A leading comment (a copyright notice) stays before `module`.
    if lines and lines[0].startswith("/-") and not lines[0].startswith("/-!"):
        while i < n:
            lead.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
    head = []
    while i < n and (IMPORT.match(lines[i]) or lines[i].strip() == "" or lines[i].startswith("--")):
        head.append(lines[i])
        i += 1
    imports = [IMPORT.match(l).group(1) for l in head if IMPORT.match(l)]
    meta = is_meta(text, imports)
    evals = not meta and evaluates(text, names)
    # Tactics next to definitions and theorems: their code needs Lean at
    # elaboration time too.
    mixed = not meta and (META_DECL.search(text) is not None or META_MARK.search(text) is not None)
    out = lead + ["module", ""]
    for l in head:
        m = IMPORT.match(l)
        if m:
            core = m.group(1) == "Lean" or m.group(1).startswith("Lean.")
            l = f"public {'meta ' if meta and core else ''}import {m.group(1)}"
            if meta and not core:
                l += f"\npublic meta import {m.group(1)}"
            if mixed and core:
                l += f"\npublic meta import {m.group(1)}"
            if evals:
                l += f"\nmeta import {m.group(1)}"
        out.append(l)
    while out and out[-1].strip() == "":
        out.pop()
    if proof and not meta:
        out += [f"import all {m}" for m in CORE_ALL]
        out += [f"import all {m}" for m, name in CORE_ALL_FOR.items() if name in text]
    out.append("")
    # The module's docstring stays right after the imports.
    if i < n and lines[i].startswith("/-!"):
        while i < n:
            out.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
        out.append("")
    out.append("public meta section" if meta else "@[expose] public section")
    out.append("")
    while i < n and lines[i].strip() == "":
        i += 1
    out += lines[i:]
    return "\n".join(out)


def main(args: list[str]) -> int:
    if not args:
        print(__doc__, file=sys.stderr)
        return 2
    files = []
    for a in args:
        p = pathlib.Path(a)
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    names = evaluating_names(LEAN)
    changed = 0
    for f in files:
        text = f.read_text()
        new = convert(text, is_proof(str(f)), names)
        if new != text:
            f.write_text(new)
            changed += 1
    print(f"{changed} of {len(files)} files converted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
