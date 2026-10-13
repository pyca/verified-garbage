"""What `check_lean_modules.py` rejects; no builds."""

import pathlib
import tempfile
import unittest

import check_lean_modules


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


class Modules(unittest.TestCase):
    def test_a_library_of_modules(self):
        with tree({"VerifiedGarbage/A.lean": "/- Copyright. -/\nmodule\n\npublic import VerifiedGarbage.B\n",
                   "VerifiedGarbage/B.lean": "-- A comment.\nmodule\n",
                   "VerifiedGarbage/Artifacts.lean": "import VerifiedGarbage.A\n"}) as d:
            self.assertEqual(check_lean_modules.problems(pathlib.Path(d)), [])

    def test_a_file_that_is_not_a_module(self):
        # A new directory is checked too: there is no list of directories.
        with tree({"VerifiedGarbage/New/A.lean": "import VerifiedGarbage.B\n",
                   "VerifiedGarbage/B.lean": "module\n"}) as d:
            [p] = check_lean_modules.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/New/A.lean: not a module"))

    def test_artifacts_lean_is_not_a_module(self):
        with tree({"VerifiedGarbage/Artifacts.lean": "module\n"}) as d:
            [p] = check_lean_modules.problems(pathlib.Path(d))
            self.assertIn("runs the audits", p)

    def test_a_module_importing_a_file_that_is_not_one(self):
        with tree({"VerifiedGarbage/A.lean": "module\n\nmeta import VerifiedGarbage.Artifacts\nimport Lean\n",
                   "VerifiedGarbage/Artifacts.lean": "import Lean\n"}) as d:
            self.assertEqual(check_lean_modules.problems(pathlib.Path(d)),
                             ["lean/VerifiedGarbage/A.lean: a module, but imports "
                              "`VerifiedGarbage.Artifacts`, which is not one"])


if __name__ == "__main__":
    unittest.main()
