"""How `modularize.py` converts files and finds unconverted ones; no builds."""

import pathlib
import tempfile
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


class NotConverted(unittest.TestCase):
    def test_the_files_that_are_not_modules(self):
        with tempfile.TemporaryDirectory() as d:
            lean = pathlib.Path(d)
            (lean / "L").mkdir()
            (lean / "L/A.lean").write_text("module\n\npublic import B\n")
            (lean / "L/B.lean").write_text("import C\n")
            (lean / "L/C.lean").write_text("-- A comment.\nmodule\n")
            self.assertEqual(modularize.not_converted(lean, ["L"]), [("L", lean / "L/B.lean")])

    def test_a_directory_s_own_files(self):
        with tempfile.TemporaryDirectory() as d:
            lean = pathlib.Path(d)
            (lean / "L/S").mkdir(parents=True)
            (lean / "L/A.lean").write_text("module\n")
            (lean / "L/S/B.lean").write_text("import C\n")
            self.assertEqual(modularize.not_converted(lean, ["L/*"]), [])
            self.assertEqual(modularize.not_converted(lean, ["L"]), [("L", lean / "L/S/B.lean")])


    def test_a_module_importing_a_file_that_is_not_one(self):
        with tempfile.TemporaryDirectory() as d:
            lean = pathlib.Path(d)
            (lean / "VerifiedGarbage/L").mkdir(parents=True)
            (lean / "VerifiedGarbage/L/A.lean").write_text(
                "module\n\npublic import VerifiedGarbage.L.B\nmeta import VerifiedGarbage.L.C\nimport Lean\n")
            (lean / "VerifiedGarbage/L/B.lean").write_text("import VerifiedGarbage.L.C\n")
            (lean / "VerifiedGarbage/L/C.lean").write_text("module\n")
            self.assertEqual(modularize.non_module_imports(lean),
                             [(lean / "VerifiedGarbage/L/A.lean", "VerifiedGarbage.L.B")])

if __name__ == "__main__":
    unittest.main()
