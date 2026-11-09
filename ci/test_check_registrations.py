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


if __name__ == "__main__":
    unittest.main()
