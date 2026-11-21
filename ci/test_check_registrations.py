"""What `check_registrations.py` rejects; no builds."""

import pathlib
import tempfile
import unittest

import check_registrations


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


class Registrations(unittest.TestCase):
    def test_bindings(self):
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\n/-! # Proven by `lit_decide` -/\n-- by decide\n"
                    "def artifacts : List Artifact := [\n"
                    "  api.artifact X86_64.target {\n"
                    "    suffix := \"_found by a mask\"\n"
                    "    verified := Proof.A.verified (.inl rfl) }]\n",
                    "VerifiedGarbage/Artifacts/C/X86_64.lean":
                    "module\ndef sign (code : Prog isa)\n"
                    "    (hsp : code.all (fun i => !isa.writesSp i) = true := by sp_safe) : Artifact :=\n"
                    "  x\n",
                    # Proofs are not reviewed by hand.
                    "VerifiedGarbage/Proof/A.lean": "module\ntheorem t : True := by trivial\n"}) as d:
            self.assertEqual(check_registrations.problems(pathlib.Path(d)), [])

    def test_a_tactic_argument(self):
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    verified := Proof.A.framed (by lit_decide) }]\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/Artifacts/A/X86_64.lean:4: a tactic proof"))

    def test_a_tactic_field(self):
        with tree({"VerifiedGarbage/Artifacts/B/X86_64.lean":
                    "module\ndef artifacts (adx : Bool) := [\n  api.artifact t {\n"
                    "    spSafe := by cases adx <;> exact h }]\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertIn(":4: a tactic proof", p)

    def test_a_default_as_a_field(self):
        # A default ends at the next field, at the same indentation.
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    spSafe := by sp_safe\n"
                    "    ofSig := by\n      of_sig\n"
                    "    verified := v }]\n"}) as d:
            self.assertEqual(check_registrations.problems(pathlib.Path(d)), [])

    def test_a_default_with_more_tactics(self):
        with tree({"VerifiedGarbage/Artifacts/B/X86_64.lean":
                    "module\ndef sign (code : Prog isa)\n"
                    "    (hsp : P code := by sp_safe <;> decide) : Artifact :=\n  x\n",
                    "VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    spSafe := by sp_safe\n      all_goals decide\n"
                    "    verified := v }]\n"}) as d:
            ps = check_registrations.problems(pathlib.Path(d))
            self.assertEqual(len(ps), 2)
            self.assertIn("Artifacts/A/X86_64.lean:4: a tactic proof", ps[0])
            self.assertIn("Artifacts/B/X86_64.lean:3: a tactic proof", ps[1])

    def test_consts(self):
        # The default finds the tables in the contract; a field of the
        # proofs' own structures may still be named `consts`.
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    consts := Impl.A.tables\n"
                    "    verified := v }]\n",
                    "VerifiedGarbage/Artifacts/B/X86_64.lean":
                    "module\n-- consts := none\ndef artifacts := [\n  api.artifact t {\n"
                    "    code := c.consts\n    Impl.myconsts := v }]\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/Artifacts/A/X86_64.lean:4: `consts`"))

    def test_stack(self):
        # The default finds the stack in the contract; a field of the
        # proofs' own structures may still be named `stack`.
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    code := c\n"
                    "    stack := 8 + Proof.A.frame\n"
                    "    verified := v }]\n",
                    "VerifiedGarbage/Artifacts/B/X86_64.lean":
                    "module\n-- stack := 8\ndef artifacts := [\n  api.artifact t {\n"
                    "    code := c.stack\n    verified := v (mystack := 8) }]\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/Artifacts/A/X86_64.lean:5: `stack`"))

    def test_a_theorem(self):
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ntheorem ok : 1 = 1 := rfl\ndef artifacts := v\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertIn(":2: a theorem", p)

    def test_a_module_docstring(self):
        # Only a title: prose on the implementation goes stale.
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\n/-! # A on x86-64 -/\ndef artifacts := []\n",
                    "VerifiedGarbage/Artifacts/B/X86_64.lean":
                    "module\n/-!\n# B on x86-64\n\nCalls `f` from a frame of 8 bytes.\n-/\n"
                    "def artifacts := []\n",
                    "VerifiedGarbage/Artifacts/C/X86_64.lean":
                    "module\n/-! Uses AVX2. -/\ndef artifacts := v\n"}) as d:
            ps = check_registrations.problems(pathlib.Path(d))
            self.assertEqual(len(ps), 2)
            self.assertIn("Artifacts/B/X86_64.lean:2: a module docstring", ps[0])
            self.assertIn("Artifacts/C/X86_64.lean:2: a module docstring", ps[1])


RV = "VerifiedGarbage/Artifacts/A/RISCV64.lean"


def rv(body: str) -> str:
    return "module\ndef artifacts : List Artifact := [\n" + body + "]\n"


class RiscV(unittest.TestCase):
    def problems(self, body: str) -> list[str]:
        with tree({RV: rv(body)}) as d:
            return check_registrations.problems(pathlib.Path(d))

    def test_bindings(self):
        # What every 64-bit RISC-V registration file states: named code and
        # a theorem about it, and the implementation's choices.
        self.assertEqual(self.problems(
            "  Spec.A.fApi.artifact RISCV64.target {\n"
            "    code := Impl.A.RISCV64.Fn.f Spec.A.rate\n"
            "    verified := Proof.A.RISCV64.f_scrubbed },\n"
            "  Spec.A.gApi.artifact RISCV64.target {\n"
            "    tables := [(\"hmac\", tables variants)]\n"
            "    code := Impl.A.RISCV64.Fn.«seal» fns\n"
            "    verified :=\n"
            "      (Proof.A.RISCV64.g_scrubbed hasLaw.law) }] ++\n"
            "  Proof.Variants.B.RISCV64.variants.map fun v =>\n"
            "    Spec.A.hApi.artifact RISCV64.target {\n"
            "      suffix := v.suffix\n"
            "      code := Impl.A.RISCV64.Fn.h v.suffix v.code\n"
            "      verified := (Proof.A.RISCV64.h v) } ++\n"
            "  Rfc6979.artifacts"), [])

    def test_other_targets(self):
        # The rule is RISC-V's: other targets still build in `Proof/`.
        with tree({"VerifiedGarbage/Artifacts/A/X86_64.lean":
                    rv("  api.artifact X86_64.target (Proof.A.X86_64.reg)")}) as d:
            self.assertEqual(check_registrations.problems(pathlib.Path(d)), [])

    def test_a_builder(self):
        [p] = self.problems("  api.artifact RISCV64.target (Proof.A.RISCV64.reg)")
        self.assertIn(f"lean/{RV}:3: a RISC-V registration not given as a record", p)

    def test_a_builder_in_the_framework(self):
        ps = self.problems("  api.artifact RISCV64.target (RISCV64.Scrub.scrubOf r h)")
        self.assertEqual(len(ps), 2)
        self.assertIn(":3: the scrub framework", ps[0])
        self.assertIn(":3: a RISC-V registration not given as a record", ps[1])

    def test_code_not_named(self):
        [p] = self.problems(
            "  api.artifact RISCV64.target {\n"
            "    code := scrub 64 0 Proof.A.code\n"
            "    verified := Proof.A.ok }")
        self.assertIn(":4: a RISC-V registration's `code`", p)

    def test_verified_not_named(self):
        ps = self.problems(
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.f\n"
            "    verified := f_scrubbed },\n"
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.g\n"
            "    verified := VerifiedScrubbed.abi (Proof.A.g_scrubbed) }")
        self.assertEqual(len(ps), 2)
        self.assertIn(":5: a RISC-V registration's `verified`", ps[0])
        self.assertIn(":8: a RISC-V registration's `verified`", ps[1])

    def test_anonymous_constructor(self):
        ps = self.problems(
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.f\n"
            "    verified := (Proof.A.f ⟨Proof.A.h, rfl⟩) }")
        self.assertEqual(len(ps), 1)
        self.assertIn(":5: an anonymous constructor", ps[0])

    def test_a_default_tactic(self):
        # Even `Registration`'s defaults, and `spSafe` is no choice either:
        # the theorem proves what they would.
        ps = self.problems(
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.f\n"
            "    spSafe := by sp_safe\n"
            "    verified := Proof.A.f }")
        self.assertEqual(len(ps), 2)
        self.assertIn(":5: a tactic proof in a RISC-V registration", ps[0])
        self.assertIn(":5: `spSafe` in a RISC-V registration", ps[1])

    def test_fields(self):
        ps = self.problems(
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.f\n"
            "    written := [(0, 8)] },\n"
            "  api.artifact RISCV64.target {\n"
            "    code := Impl.A.g\n"
            "    code := Impl.A.g\n"
            "    verified := Proof.A.g }")
        self.assertEqual(len(ps), 3)
        self.assertIn(":5: `written` in a RISC-V registration", ps[0])
        self.assertIn(":3: a RISC-V registration without exactly one `verified :=`", ps[1])
        self.assertIn(":6: a RISC-V registration without exactly one `code :=`", ps[2])


if __name__ == "__main__":
    unittest.main()
