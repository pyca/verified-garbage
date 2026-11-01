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
                   "VerifiedGarbage/B.lean": "-- A comment.\nmodule\n"}) as d:
            self.assertEqual(check_lean_modules.problems(pathlib.Path(d)), [])

    def test_a_file_that_is_not_a_module(self):
        # A new directory is checked too: there is no list of directories.
        with tree({"VerifiedGarbage/New/A.lean": "import VerifiedGarbage.B\n",
                   "VerifiedGarbage/B.lean": "module\n"}) as d:
            [p] = check_lean_modules.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/New/A.lean: not a module"))

    def test_a_long_header_comment(self):
        # Only the header is read; a comment before `module` may span lines.
        with tree({"VerifiedGarbage/A.lean": "/- Copyright.\n\nLicensed. -/\n-- More.\nmodule\n"}) as d:
            self.assertEqual(check_lean_modules.problems(pathlib.Path(d)), [])

    def test_a_module_docstring_does_not_start_one(self):
        with tree({"VerifiedGarbage/A.lean": "/-! # A -/\nmodule\n"}) as d:
            [p] = check_lean_modules.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbage/A.lean: not a module"))

    def test_a_test_that_is_not_a_module(self):
        with tree({"VerifiedGarbageTest/A.lean": "import VerifiedGarbage.B\n",
                   "VerifiedGarbage/B.lean": "module\n"}) as d:
            [p] = check_lean_modules.problems(pathlib.Path(d))
            self.assertTrue(p.startswith("lean/VerifiedGarbageTest/A.lean: not a module"))


if __name__ == "__main__":
    unittest.main()
