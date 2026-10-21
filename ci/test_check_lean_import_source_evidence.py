"""Lean index versions, stale headers and resolved-reference ownership."""

import json
import pathlib
import tempfile
import unittest

import lean_source_evidence as source


class Index(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.path = self.root / "A.ilean"
        self.data = {"version": 5, "module": "A", "directImports": [["B", False, False, False]],
                     "references": {json.dumps({"c": {"m": "B", "n": "B.f"}}): {"usages": [[2, 0, 2, 1]]},
                                    json.dumps({"c": {"m": "C", "n": "C.f"}}): {"usages": []},
                                    json.dumps({"c": {"m": "A", "n": "A.f"}}): {"usages": [[3, 0, 3, 1]]}},
                     "decls": {"VG.A.f": [0, 0, 0, 1], "_private.A.0.Hidden.f": [0, 0, 0, 1]}}
        self.path.write_text(json.dumps(self.data))

    def read(self, imports=None):
        return source.read(self.root, "A", imports or [("B", True, False, False)], build=self.root)

    def test_only_resolved_external_uses_count(self):
        self.assertEqual(source.references(self.read()), {"B"})

    def test_namespace_evidence_is_positive_and_ignores_mangled_private_names(self):
        self.assertEqual(source.namespaces(self.read()), {"VG", "VG.A"})

    def test_stale_import_visibility_is_rejected(self):
        with self.assertRaisesRegex(source.StaleIndex, "header differs"):
            self.read([("B", False, False, False)])

    def test_unsupported_version_is_not_treated_as_no_references(self):
        self.data["version"] = 999
        self.path.write_text(json.dumps(self.data))
        with self.assertRaisesRegex(source.StaleIndex, "unsupported"):
            self.read()

    def test_missing_index_is_not_treated_as_no_references(self):
        self.path.unlink()
        with self.assertRaisesRegex(source.StaleIndex, "build the module first"):
            self.read()

    def test_nested_comments_strings_and_character_quotes_are_masked(self):
        text = ('/- namespace Fake\n/- nested -/\nmacro_rules\n-/\n'
                'def s := r#"a \" -- macro_rules"#\n'
                "def c := '\"'\n"
                'namespace Actual\nopen Actual\n')
        code = source.code_only(text)
        self.assertEqual(code.count("\n"), text.count("\n"))
        self.assertNotIn("Fake", code)
        self.assertNotIn("macro_rules", code)
        self.assertIn("namespace Actual", code)
        self.assertIn("open Actual", code)

    def test_dots_inside_quoted_identifiers_are_not_namespace_separators(self):
        self.assertEqual(source.namespaces({"decls": {"VG.«a.b».f": []}}), {"VG", "VG.«a.b»"})


if __name__ == "__main__":
    unittest.main()
