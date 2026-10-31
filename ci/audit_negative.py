#!/usr/bin/env python3
"""Checks that the emitter's audits reject an axiom and a compiler override hidden
in Lean modules.

The audits read what each constant depends on from the records every module of
this project writes when it is built (`TCB/AuditRecords.lean`), not from the
proofs, which a module importing another does not see. This test proves that the
records carry them across modules, and through a private import, which hides a
module from the modules that import the importer. It adds to a module that an
artifact depends on (`Spec/Selftest.lean`) `axiom vg_bad : False`, a theorem proven
from it, and `vg_bad_id`, the identity, with `@[implemented_by]` of a function that
is not, which `add` (that the artifact's contract uses) applies; and adds a module
with another such axiom, `Proof/Selftest/AuditPrivate.lean`, which the self-test's
proof imports with a plain `import`. It proves `add_correct` from both theorems, and
checks that `EmitOne.lean --check Selftest.X86_64` fails with the axiom audit's
`depends on non-standard axioms: [...]`, listing both `VG.Spec.Selftest.vg_bad` and
`VG.Proof.Selftest.AuditPrivate.vg_bad`, and with the override audit's
`@[implemented_by] on VG.Spec.Selftest.vg_bad_id` (Lean reports each command's error
and goes on to the next, so one build checks all three).

It edits the files in place, after copying them to a temporary directory,
and restores them from there (and deletes the module it added) whatever
happens, then checks with `git diff` and `git status` that the tree is as it
was: the axiom never reaches the tree that is committed.

Run it from the repository root after a full build (CI runs it
last in the job that assembles the build, after that build is saved): it
rebuilds the few modules of the self-test that the edits change, and leaves
them built from the edited files.

  audit_negative.py
"""

import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

LEAN = pathlib.Path("lean")
# A module (`Spec/` is converted), and a file whose proof the artifact uses.
MODULE = LEAN / "VerifiedGarbage" / "Spec" / "Selftest.lean"
PROOF = LEAN / "VerifiedGarbage" / "Proof" / "Selftest" / "X86_64.lean"
TARGET = "Selftest.X86_64"
AXIOM = "VG.Spec.Selftest.vg_bad"

INJECTED = """
/-- Not in the tree: `ci/audit_negative.py` adds it to check the audit. -/
axiom vg_bad : False

theorem vg_bad_thm : False := vg_bad

def vg_bad_impl (x : BitVec 64) : BitVec 64 := x + 1

/-- Not in the tree: compiled code runs `vg_bad_impl` in its place. -/
@[implemented_by vg_bad_impl] def vg_bad_id (x : BitVec 64) : BitVec 64 := x
"""

# `add`'s definition, and what the test makes it.
ADD = "def add (a b : BitVec 64) : BitVec 64 := a + b"
ADD_BAD = "def add (a b : BitVec 64) : BitVec 64 := vg_bad_id (a + b)"
OVERRIDE = "@[implemented_by] on VG.Spec.Selftest.vg_bad_id"

# The self-test's proof: its first theorem, proven from the axiom instead.
CORRECT = "theorem add_correct "

# The second case: a module with the axiom, imported privately.
PRIVATE = LEAN / "VerifiedGarbage" / "Proof" / "Selftest" / "AuditPrivate.lean"
PRIVATE_MODULE = "VerifiedGarbage.Proof.Selftest.AuditPrivate"
PRIVATE_AXIOM = "VG.Proof.Selftest.AuditPrivate.vg_bad"
PRIVATE_TEXT = """module

/-! Not in the tree: `ci/audit_negative.py` adds it to check the audit. -/

public section

namespace VG.Proof.Selftest.AuditPrivate

axiom vg_bad : False

theorem vg_bad_thm : False := vg_bad

end VG.Proof.Selftest.AuditPrivate
"""


def is_module(text: str) -> bool:
    return any(l.strip() == "module" for l in text.split("\n")[:5])


def inject_module(text: str) -> str:
    """`text` with the axiom, its theorem and `vg_bad_id` before `add` (with its
    documentation), which applies `vg_bad_id`."""
    at = text.find(ADD)
    doc = text.rfind("/--", 0, at)
    if at < 0 or doc < 0:
        raise SystemExit(f"{MODULE}: no `{ADD}` after a documentation comment")
    return text[:doc] + INJECTED.lstrip("\n") + "\n" + text[doc:].replace(ADD, ADD_BAD, 1)


def inject_proof(text: str, proof: str) -> str:
    """`text` with `add_correct`'s proof replaced by one from `proof`, a
    proof of `False`."""
    start = text.find(CORRECT)
    if start < 0:
        raise SystemExit(f"{PROOF}: no `{CORRECT.strip()}`")
    body = text.find(":= by", start)
    end = text.find("\n\n", body)
    if body < 0 or end < 0:
        raise SystemExit(f"{PROOF}: `add_correct` is not `:= by …` followed by a blank line")
    return text[:body] + f":=\n  {proof}.elim" + text[end:]


def inject_private_import(text: str) -> str:
    """`text` (a module) with a plain `import` of the module with the axiom,
    after its last import, and `add_correct` proven from both axioms'
    theorems (each must reach the audit)."""
    lines = text.split("\n")
    last = max(i for i, l in enumerate(lines) if IMPORT_LINE.match(l))
    lines.insert(last + 1, f"import {PRIVATE_MODULE}")
    both = "⟨Spec.Selftest.vg_bad_thm, VG.Proof.Selftest.AuditPrivate.vg_bad_thm⟩"
    return inject_proof("\n".join(lines), f"({both} : False ∧ False).2")


IMPORT_LINE = re.compile(r"^(public\s+)?(meta\s+)?import\s")


def emit_check(edits: dict, added: pathlib.Path | None = None) -> str | None:
    """Writes `edits` (file: new text) and `added` (with `PRIVATE_TEXT`), runs
    `EmitOne.lean --check` on the self-test, restores the files and deletes
    `added` (and its build), and returns the output if it failed, else
    `None`."""
    with tempfile.TemporaryDirectory() as tmp:
        saved = {p: pathlib.Path(tmp) / p.name for p in edits}
        for p, copy in saved.items():
            shutil.copy2(p, copy)
        try:
            if added is not None:
                added.write_text(PRIVATE_TEXT)
            for p, text in edits.items():
                p.write_text(text)
            r = subprocess.run(["lake", "env", "lean", "--run", "EmitOne.lean", "--check", TARGET],
                               cwd=LEAN, capture_output=True, text=True)
        finally:
            for p, copy in saved.items():
                shutil.copy2(copy, p)
            if added is not None:
                added.unlink(missing_ok=True)
                build = LEAN / ".lake" / "build"
                for d in ("lib/lean", "ir"):
                    for f in (build / d).glob(f"{added.relative_to(LEAN).with_suffix('')}.*"):
                        f.unlink()
    return None if r.returncode == 0 else r.stdout + r.stderr


# The audit's error: the axioms it found, as a Lean list.
REJECTED = re.compile(r"depends on non-standard axioms: \[([^\]]*)\]")


def rejected(out: str | None) -> bool:
    """Whether the audits rejected both axioms and the override (`out`, from
    `emit_check`)."""
    found = REJECTED.search(out or "")
    axioms = {a.strip() for a in found.group(1).split(",")} if found else set()
    ok = True
    for axiom, how in ((AXIOM, "in a module"), (PRIVATE_AXIOM, "behind a private import")):
        if axiom in axioms:
            print(f"the audit rejects an axiom {how}: `{axiom}`")
        else:
            print(f"EmitOne.lean --check {TARGET} did not reject `{axiom}`: "
                  f"the axiom audit no longer sees an axiom {how}", file=sys.stderr)
            ok = False
    if OVERRIDE in (out or ""):
        print(f"the audit rejects a compiler override in a module: `{OVERRIDE}`")
    else:
        print(f"EmitOne.lean --check {TARGET} did not report `{OVERRIDE}`: the override "
              "audit no longer sees an override in a module", file=sys.stderr)
        ok = False
    if not ok:
        print(out or "", file=sys.stderr)
    return ok


def main() -> int:
    for f in (MODULE, PROOF):
        if not is_module(f.read_text()):
            raise SystemExit(f"{f} is not a module: the test needs one")
    if PRIVATE.exists():
        raise SystemExit(f"{PRIVATE} exists: the test adds it")
    out = emit_check({MODULE: inject_module(MODULE.read_text()),
                      PROOF: inject_private_import(PROOF.read_text())}, PRIVATE)
    if (subprocess.run(["git", "diff", "--quiet", "--", str(MODULE), str(PROOF)]).returncode != 0
            or PRIVATE.exists()):
        print(f"{MODULE} or {PROOF} was not restored, or {PRIVATE} not deleted", file=sys.stderr)
        return 1
    return 0 if rejected(out) else 1


if __name__ == "__main__":
    sys.exit(main())
