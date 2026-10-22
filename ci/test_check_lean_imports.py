"""What `check_lean_imports.py` rejects in TCB/; no builds."""

import pathlib
import tempfile
import unittest

import check_lean_imports


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


class TcbLemmas(unittest.TestCase):
    def test_definitions_only(self):
        # The words in comments and strings, and in other directories, are not lemmas.
        with tree({"lean/VerifiedGarbage/TCB/A.lean":
                   "module\n/-- Not a theorem. -/\ndef a : Nat := 1\n-- lemma\ndef s := \"theorem \"\n",
                   "lean/VerifiedGarbage/Proof/A.lean": "module\ntheorem t : True := trivial\n"}) as d:
            lean = pathlib.Path(d) / "lean" / "VerifiedGarbage"
            self.assertEqual(check_lean_imports.tcb_lemmas(lean), [])

    def test_a_lemma(self):
        with tree({"lean/VerifiedGarbage/TCB/X/Isa.lean":
                   "module\ndef a : Nat := 1\n\n@[simp] theorem a_eq : a = 1 := rfl\nprivate lemma b : True := trivial\n"}) as d:
            lean = pathlib.Path(d) / "lean" / "VerifiedGarbage"
            self.assertEqual(check_lean_imports.tcb_lemmas(lean), [
                "lean/VerifiedGarbage/TCB/X/Isa.lean:4: a theorem in TCB/, which holds definitions only; "
                "prove it under Proof/",
                "lean/VerifiedGarbage/TCB/X/Isa.lean:5: a lemma in TCB/, which holds definitions only; "
                "prove it under Proof/"])


if __name__ == "__main__":
    unittest.main()
