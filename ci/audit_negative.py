#!/usr/bin/env python3
"""Checks that the axiom audit rejects an axiom hidden in a Lean module, and
that the audits refuse to run in one.

A module sees the theorems it imports from other modules as axioms, without
their proofs, so the audits run in the emitter's driver, a file that is not
a module, which sees every proof (`TCB/Axioms.lean`). This test proves that
they still see through modules: it adds `axiom vg_bad : False` and a theorem
proven from it to a module that an artifact depends on (`Spec/Selftest.lean`),
makes the self-test's proof use that theorem, and checks that
`EmitOne.lean --check Selftest.X86_64` fails with the audit's
`depends on non-standard axioms: [VG.Spec.Selftest.vg_bad]`.

It then checks the same through a private import, which hides a module from
the modules that import the importer, but not from a file that is not a
module: it adds a module with the axiom, `Proof/Selftest/AuditPrivate.lean`,
imports it into the self-test's proof with a plain `import`, proves
`add_correct` from it, and expects
`depends on non-standard axioms: [VG.Proof.Selftest.AuditPrivate.vg_bad]`.

It edits the files in place, after copying them to a temporary directory,
and restores them from there (and deletes the module it added) whatever
happens, then checks with `git diff` and `git status` that the tree is as it
was: the axiom never reaches the tree that is committed.

It also runs each audit command in a scratch module, outside the tree, and
checks that each refuses to run there.

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
"""

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
    """`text` with the axiom and its theorem at the end of its namespace."""
    end = "end VG.Spec.Selftest"
    if end not in text:
        raise SystemExit(f"{MODULE}: no `{end}` to add the axiom before")
    return text.replace(end, INJECTED.lstrip("\n") + "\n" + end, 1)


def inject_proof(text: str, proof: str = "Spec.Selftest.vg_bad_thm") -> str:
    """`text` with `add_correct`'s proof replaced by one from `proof`."""
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
    after its last import, and `add_correct` proven from it."""
    lines = text.split("\n")
    last = max(i for i, l in enumerate(lines) if IMPORT_LINE.match(l))
    lines.insert(last + 1, f"import {PRIVATE_MODULE}")
    return inject_proof("\n".join(lines), "VG.Proof.Selftest.AuditPrivate.vg_bad_thm")


IMPORT_LINE = re.compile(r"^(public\s+)?(meta\s+)?import\s")


# Each audit command, and an argument to give it in the scratch module.
AUDITS = [("#assert_standard_axioms", "VG.standardAxioms"),
          ("#assert_no_compiler_overrides", "VG.standardAxioms"),
          ("#assert_spec_origin", "")]


def audits_refuse_modules() -> bool:
    """Whether each audit command fails in a module, saying why."""
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for cmd, arg in AUDITS:
            f = pathlib.Path(tmp) / "Audit.lean"
            f.write_text("module\n\nimport VerifiedGarbage.TCB.Audit\nimport VerifiedGarbage.TCB.Axioms\n\n"
                         f"{cmd} {arg}\n".replace(" \n", "\n"))
            r = subprocess.run(["lake", "env", "lean", str(f)], cwd=LEAN, capture_output=True, text=True)
            expected = f"{cmd} must run in a file that is not a module"
            if r.returncode == 0 or expected not in r.stdout + r.stderr:
                print(r.stdout + r.stderr, file=sys.stderr)
                print(f"{cmd} ran in a module", file=sys.stderr)
                ok = False
    return ok


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


def rejected(out: str | None, axiom: str, how: str) -> bool:
    """Whether the audit rejected `axiom` (`out`, from `emit_check`)."""
    expected = f"depends on non-standard axioms: [{axiom}]"
    if out is None or expected not in out:
        print(out or "", file=sys.stderr)
        print(f"EmitOne.lean --check {TARGET} did not fail with `{expected}`: "
              f"the axiom audit no longer sees an axiom {how}", file=sys.stderr)
        return False
    print(f"the audit rejects an axiom {how}: `{expected}`")
    return True


def main() -> int:
    if not audits_refuse_modules():
        return 1
    print("the audits refuse to run in a module")
    for f in (MODULE, PROOF):
        if not is_module(f.read_text()):
            raise SystemExit(f"{f} is not a module: the test needs one")
    if PRIVATE.exists():
        raise SystemExit(f"{PRIVATE} exists: the test adds it")
    in_module = emit_check({MODULE: inject_module(MODULE.read_text()),
                            PROOF: inject_proof(PROOF.read_text())})
    private = emit_check({PROOF: inject_private_import(PROOF.read_text())}, PRIVATE)
    if (subprocess.run(["git", "diff", "--quiet", "--", str(MODULE), str(PROOF)]).returncode != 0
            or PRIVATE.exists()):
        print(f"{MODULE} or {PROOF} was not restored, or {PRIVATE} not deleted", file=sys.stderr)
        return 1
    ok = rejected(in_module, AXIOM, "in a module")
    return 0 if rejected(private, PRIVATE_AXIOM, "behind a private import") and ok else 1


if __name__ == "__main__":
    sys.exit(main())
