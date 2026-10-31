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
                    "module\n/-! Proven by `lit_decide` -/\n-- by decide\n"
                    "def artifacts : List Artifact := [\n"
                    "  api.artifact X86_64.target {\n"
                    "    suffix := \"_found by a mask\"\n"
                    "    verified := Proof.A.verified (.inl rfl) }]\n",
                    "VerifiedGarbage/Generic/B/X86_64/C.lean":
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
        with tree({"VerifiedGarbage/Generic/A/X86_64/B.lean":
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
        with tree({"VerifiedGarbage/Generic/A/X86_64/B.lean":
                    "module\ndef sign (code : Prog isa)\n"
                    "    (hsp : P code := by sp_safe <;> decide) : Artifact :=\n  x\n",
                    "VerifiedGarbage/Artifacts/A/X86_64.lean":
                    "module\ndef artifacts := [\n  api.artifact t {\n"
                    "    spSafe := by sp_safe\n      all_goals decide\n"
                    "    verified := v }]\n"}) as d:
            ps = check_registrations.problems(pathlib.Path(d))
            self.assertEqual(len(ps), 2)
            self.assertIn("Artifacts/A/X86_64.lean:4: a tactic proof", ps[0])
            self.assertIn("Generic/A/X86_64/B.lean:3: a tactic proof", ps[1])

    def test_a_theorem(self):
        with tree({"VerifiedGarbage/Variants/A/X86_64/B.lean":
                    "module\ntheorem ok : 1 = 1 := rfl\ndef variant := v\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertIn(":2: a theorem", p)


if __name__ == "__main__":
    unittest.main()
