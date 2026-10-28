"""What `check_lean_single_importer.py` rejects; no builds."""

import pathlib
import tempfile
import unittest

import check_lean_single_importer as check

P = "VerifiedGarbage/Proof/"


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


def mod(*imports: str, body: str = "") -> str:
    return "/- Copyright. -/\nmodule\n\n" + "".join(i + "\n" for i in imports) + "\n/-! # Doc -/\n" + body


class SingleImporter(unittest.TestCase):
    def problems(self, files: dict, added: set[str]) -> list[str]:
        with tree(files) as d:
            return check.problems(pathlib.Path(d), added)

    def test_a_new_module_with_one_proof_importer(self):
        [p] = self.problems({P + "A.lean": mod(), P + "B.lean": mod("import VerifiedGarbage.Proof.A")},
                            {"VerifiedGarbage.Proof.A"})
        self.assertTrue(p.startswith("lean/VerifiedGarbage/Proof/A.lean: new module imported only by "
                                     "VerifiedGarbage.Proof.B"), p)

    def test_public_imports_count(self):
        [_] = self.problems({P + "A.lean": mod(), P + "B.lean": mod("public import VerifiedGarbage.Proof.A")},
                            {"VerifiedGarbage.Proof.A"})

    def test_only_new_modules_are_checked(self):
        self.assertEqual(self.problems({P + "A.lean": mod(), P + "B.lean": mod("import VerifiedGarbage.Proof.A")},
                                       set()), [])

    def test_two_importers_or_none(self):
        files = {P + "A.lean": mod(), P + "B.lean": mod("import VerifiedGarbage.Proof.A"),
                 P + "C.lean": mod("import VerifiedGarbage.Proof.A")}
        self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [])
        self.assertEqual(self.problems({P + "A.lean": mod()}, {"VerifiedGarbage.Proof.A"}), [])

    def test_an_importer_of_another_kind(self):
        for importer in ("VerifiedGarbage/Generic/Foo/Arm/A.lean", "VerifiedGarbage/Artifacts/A/Arm.lean",
                         "VerifiedGarbageTest/A.lean", "Emit.lean"):
            files = {P + "A.lean": mod(), importer: mod("import VerifiedGarbage.Proof.A")}
            self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [], importer)

    def test_meta_or_all_imports(self):
        for imp in ("meta import VerifiedGarbage.Proof.A", "import all VerifiedGarbage.Proof.A"):
            files = {P + "A.lean": mod(), P + "B.lean": mod(imp)}
            self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [], imp)

    def test_conventions(self):
        for name in ("Framework/A", "Variants/X/Arm/A", "ALit", "Lit", "X/Instances"):
            m = "VerifiedGarbage.Proof." + name.replace("/", ".")
            files = {P + name + ".lean": mod(), P + "B.lean": mod("import " + m)}
            self.assertEqual(self.problems(files, {m}), [], name)
        for body in ("materialize_code foo\n", "taint_summary fooSum : x\n", "public meta section\n"):
            files = {P + "A.lean": mod(body=body), P + "B.lean": mod("import VerifiedGarbage.Proof.A")}
            self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [], body)

    def test_a_stated_reason(self):
        files = {P + "A.lean": mod(body="-- separate module: its proofs take 12 s, its imports 1 s\n"),
                 P + "B.lean": mod("import VerifiedGarbage.Proof.A")}
        self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [])
        # An empty reason is none.
        files[P + "A.lean"] = mod(body="-- separate module:\n")
        [_] = self.problems(files, {"VerifiedGarbage.Proof.A"})

    def test_only_proof_modules(self):
        files = {"VerifiedGarbage/Impl/A.lean": mod(), "VerifiedGarbage/Impl/B.lean": mod("import VerifiedGarbage.Impl.A")}
        self.assertEqual(self.problems(files, {"VerifiedGarbage.Impl.A"}), [])

    def test_header_ends_at_the_first_command(self):
        # An `import` in a doc comment after the header is not one.
        files = {P + "A.lean": mod(), P + "B.lean": mod(body="/-- see\nimport VerifiedGarbage.Proof.A -/\n")}
        self.assertEqual(check.header(files[P + "B.lean"]), [])
        self.assertEqual(self.problems(files, {"VerifiedGarbage.Proof.A"}), [])


if __name__ == "__main__":
    unittest.main()
