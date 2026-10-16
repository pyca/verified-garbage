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
                    "    notes := [\"found by a mask\"]\n"
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

    def test_a_theorem(self):
        with tree({"VerifiedGarbage/Variants/A/X86_64/B.lean":
                    "module\ntheorem ok : 1 = 1 := rfl\ndef variant := v\n"}) as d:
            [p] = check_registrations.problems(pathlib.Path(d))
            self.assertIn(":2: a theorem", p)


if __name__ == "__main__":
    unittest.main()
