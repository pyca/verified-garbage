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


class Visibility(unittest.TestCase):
    # A imports B publicly, B imports C publicly; A's proofs use C, its
    # statements only B; D (outside the project) is imported publicly by B.
    MODS = {
        "VerifiedGarbage.C": ([], set(), set(), False, {"VG.C"}),
        "Ext.D": ([], set(), set(), False, set()),
        "VerifiedGarbage.B": ([("VerifiedGarbage.C", True, False), ("Ext.D", True, False)],
                              set(), {"VerifiedGarbage.C"}, False, {"VG.B"}),
        "VerifiedGarbage.A": ([("VerifiedGarbage.B", True, False)],
                              {"VerifiedGarbage.B"}, {"VerifiedGarbage.B", "VerifiedGarbage.C"}, False, set()),
    }

    def plan(self, mods=None, src=None):
        mods = mods or self.MODS
        src = {n: "module\n" for n in mods} | (src or {})
        orig = modularize.module_path
        modularize.module_path = lambda n: type("P", (), {"exists": lambda s: True,
                                                          "read_text": lambda s: src.get(n, "")})()
        try:
            return modularize.plan_visibility(mods)
        finally:
            modularize.module_path = orig

    def test_demotes_what_the_public_surface_does_not_need(self):
        plan = self.plan()
        # B's statements mention nothing: C becomes private, D (outside the
        # project) stays public; A, whose proofs use C, imports it directly.
        self.assertEqual(plan["VerifiedGarbage.B"], (["VerifiedGarbage.C"], [], []))
        self.assertEqual(plan["VerifiedGarbage.A"], ([], [], ["VerifiedGarbage.C"]))

    def test_keeps_what_an_open_needs(self):
        # A uses only B but opens `VG.C`, which only C declares: once B's
        # import of C is private, A imports C itself.
        mods = dict(self.MODS)
        mods["VerifiedGarbage.A"] = ([("VerifiedGarbage.B", True, False)],
                                     {"VerifiedGarbage.B"}, {"VerifiedGarbage.B"}, False, set())
        plan = self.plan(mods, {"VerifiedGarbage.A": "module\nnamespace VG.A\nopen VG.C\nend VG.A\n"})
        self.assertEqual(plan["VerifiedGarbage.B"], (["VerifiedGarbage.C"], [], []))
        self.assertEqual(plan["VerifiedGarbage.A"], ([], [], ["VerifiedGarbage.C"]))
        self.assertNotIn("VerifiedGarbage.A", self.plan(mods))

    def test_opened_namespaces(self):
        self.assertEqual(modularize.opened_namespaces("namespace VG.P\nopen X.Y Z (a) in\nopen scoped W\n"),
                         [["VG.P.X.Y", "VG.X.Y", "X.Y"], ["VG.P.Z", "VG.Z", "Z"], ["VG.P.W", "VG.W", "W"]])

    def test_apply(self):
        text = "module\n\npublic import X\nmeta import X\nimport all Init.Data.Array.Basic\n\n/-! Doc. -/\n"
        self.assertEqual(modularize.apply_visibility(text, ["X"], ["P"], ["Q"]),
                         "module\n\nimport X\nmeta import X\nimport all Init.Data.Array.Basic\n"
                         "public import P\nimport Q\nmeta import P\nmeta import Q\n\n/-! Doc. -/\n")
        self.assertEqual(modularize.apply_visibility(text, [], [], ["Q"]),
                         "module\n\npublic import X\nmeta import X\nimport all Init.Data.Array.Basic\n"
                         "import Q\nmeta import Q\n\n/-! Doc. -/\n")


if __name__ == "__main__":
    unittest.main()
