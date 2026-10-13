"""How `modularize.py` converts files; no builds."""

import unittest

import modularize


class Convert(unittest.TestCase):
    def test_a_plain_file(self):
        out = modularize.convert("import A.B\n\n/-! Docs. -/\n\nnamespace X\ndef y := 1\nend X\n")
        self.assertEqual(out, "module\n\npublic import A.B\n\n/-! Docs. -/\n\n"
                              "@[expose] public section\n\nnamespace X\ndef y := 1\nend X\n")

    def test_idempotent(self):
        once = modularize.convert("-- A comment.\nimport A\n\ndef y := 1\n")
        self.assertEqual(modularize.convert(once), once)

    def test_meta_code(self):
        out = modularize.convert("import Lean.Elab.Tactic.Basic\n\nelab \"t\" : tactic => pure ()\n")
        self.assertIn("public meta import Lean.Elab.Tactic.Basic\n", out)
        self.assertIn("public meta section\n", out)


if __name__ == "__main__":
    unittest.main()
