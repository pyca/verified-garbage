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

It edits the two files in place, after copying them to a temporary
directory, and restores them from there whatever happens, then checks with
`git diff` that the tree is as it was: the axiom never reaches the tree that
is committed.

It also runs each audit command in a scratch module, outside the tree, and
checks that each refuses to run there.

Run it from the repository root after a full build (CI runs it
last in the job that assembles the build, after that build is saved): it
rebuilds the few modules of the self-test that the edits change, and leaves
them built from the edited files.

  audit_negative.py
"""

import pathlib
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


def is_module(text: str) -> bool:
    return any(l.strip() == "module" for l in text.split("\n")[:5])


def inject_module(text: str) -> str:
    """`text` with the axiom and its theorem at the end of its namespace."""
    end = "end VG.Spec.Selftest"
    if end not in text:
        raise SystemExit(f"{MODULE}: no `{end}` to add the axiom before")
    return text.replace(end, INJECTED.lstrip("\n") + "\n" + end, 1)


def inject_proof(text: str) -> str:
    """`text` with `add_correct`'s proof replaced by one from the axiom."""
    start = text.find(CORRECT)
    if start < 0:
        raise SystemExit(f"{PROOF}: no `{CORRECT.strip()}`")
    body = text.find(":= by", start)
    end = text.find("\n\n", body)
    if body < 0 or end < 0:
        raise SystemExit(f"{PROOF}: `add_correct` is not `:= by …` followed by a blank line")
    return text[:body] + ":=\n  Spec.Selftest.vg_bad_thm.elim" + text[end:]


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


def main() -> int:
    if not audits_refuse_modules():
        return 1
    print("the audits refuse to run in a module")
    if not is_module(MODULE.read_text()):
        raise SystemExit(f"{MODULE} is not a module: the test needs one")
    with tempfile.TemporaryDirectory() as tmp:
        saved = {p: pathlib.Path(tmp) / p.name for p in (MODULE, PROOF)}
        for p, copy in saved.items():
            shutil.copy2(p, copy)
        try:
            MODULE.write_text(inject_module(MODULE.read_text()))
            PROOF.write_text(inject_proof(PROOF.read_text()))
            r = subprocess.run(["lake", "env", "lean", "--run", "EmitOne.lean", "--check", TARGET],
                               cwd=LEAN, capture_output=True, text=True)
        finally:
            for p, copy in saved.items():
                shutil.copy2(copy, p)
    out = r.stdout + r.stderr
    if subprocess.run(["git", "diff", "--quiet", "--", str(MODULE), str(PROOF)]).returncode != 0:
        print(f"{MODULE} or {PROOF} was not restored", file=sys.stderr)
        return 1
    expected = f"depends on non-standard axioms: [{AXIOM}]"
    if r.returncode == 0 or expected not in out:
        print(out, file=sys.stderr)
        print(f"EmitOne.lean --check {TARGET} did not fail with `{expected}`: "
              "the axiom audit no longer sees an axiom in a module", file=sys.stderr)
        return 1
    print(f"the audit rejects an axiom in a module: `{expected}`")
    return 0


if __name__ == "__main__":
    sys.exit(main())
