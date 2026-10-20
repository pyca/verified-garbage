"""The public-import check's reading of `lake shake`, on a small project; no
builds."""

import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest import mock

import check_lean_public_imports as check


class Check(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.lean = pathlib.Path(tmp.name) / "lean"
        self.deps = pathlib.Path(tmp.name) / "deps"
        for p in ("LEAN",):
            patch = mock.patch.object(check, p, self.lean)
            patch.start()
            self.addCleanup(patch.stop)
        self.write({
            "lean/VerifiedGarbage/A.lean": "module\n\npublic import VerifiedGarbage.B\npublic import VerifiedGarbage.Seal\n",
            "lean/VerifiedGarbage/B.lean": "module\n\npublic import VerifiedGarbage.Seal\npublic import Dep.X\n",
            "lean/VerifiedGarbage/C.lean": "module\n\npublic import VerifiedGarbage.B\nimport VerifiedGarbage.A\n",
            "lean/VerifiedGarbage/Seal.lean": "module\n\nattribute [irreducible] f\n",
            "lean/VerifiedGarbage/Artifacts.lean": "import VerifiedGarbage.A\n",
            "lean/VerifiedGarbage/Legacy.lean": "import VerifiedGarbage.A\n",
            "deps/Dep/X.lean": "module\n",
        })
        self.graph = check.Graph([self.lean, self.deps])

    def write(self, files):
        for name, text in files.items():
            p = self.lean.parent / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)

    def problems(self, mod, rem, add=()):
        f = str(self.lean / (mod.replace(".", "/") + ".lean"))
        return check.problems([mod], {f: (list(rem), list(add))}, self.graph)

    def test_a_public_import_used_privately(self):
        p, _ = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"], ["import VerifiedGarbage.B"])
        self.assertIn("lean/VerifiedGarbage/C.lean:3: `public import VerifiedGarbage.B`", p)
        self.assertIn("make it `import VerifiedGarbage.B`", p)

    def test_an_import_shake_keeps_public(self):
        # Shake replaces it by more specific imports, `B` among them, public.
        self.assertEqual(self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"],
                                       ["public import VerifiedGarbage.B"]), [])

    def test_never_a_module_with_side_effects(self):
        self.assertEqual(self.problems("VerifiedGarbage.B", ["public import VerifiedGarbage.Seal"]), [])

    def test_never_a_dependency(self):
        self.assertEqual(self.problems("VerifiedGarbage.B", ["public import Dep.X"]), [])

    def test_private_and_meta_imports_are_not_asked_about(self):
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A",
                                                             "public meta import VerifiedGarbage.B"]), [])

    def test_what_making_it_private_would_hide(self):
        # C passes on Seal and Dep.X only through B: making B private names them.
        [p, keep] = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"])
        self.assertIn("`public import Dep.X`, `public import VerifiedGarbage.Seal`", keep)
        # A passes on Seal itself too.
        [p, keep] = self.problems("VerifiedGarbage.A", ["public import VerifiedGarbage.B"])
        self.assertEqual(keep.split(": ", 1)[1].count("public import"), 1)
        self.assertIn("`public import Dep.X`", keep)

    def test_only_what_the_change_made_public(self):
        # C's `public import B` was public at the base: not asked about.
        f = str(self.lean / "VerifiedGarbage/C.lean")
        shaken = {f: (["public import VerifiedGarbage.B"], ["import VerifiedGarbage.B"])}
        self.assertEqual(check.problems(["VerifiedGarbage.C"], shaken, self.graph, {"VerifiedGarbage.C": set()}), [])
        [p, _] = check.problems(["VerifiedGarbage.C"], shaken, self.graph,
                                {"VerifiedGarbage.C": {"VerifiedGarbage.B"}})
        self.assertIn("`public import VerifiedGarbage.B`", p)

    def test_new_public_imports(self):
        root = self.lean.parent
        git = lambda *a: subprocess.run(["git", "-C", str(root), *a], check=True, capture_output=True)
        git("init", "-q")
        git("add", ".")
        git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "c")
        self.write({"lean/VerifiedGarbage/C.lean":
                    "module\n\npublic import VerifiedGarbage.B\npublic import VerifiedGarbage.A\n"})
        with mock.patch.object(check, "ROOT", root):
            self.assertEqual(check.new_public("VerifiedGarbage.C", "HEAD"), {"VerifiedGarbage.A"})
            self.assertIsNone(check.new_public("VerifiedGarbage.C", None))
            self.assertIsNone(check.new_public("VerifiedGarbage.New", "HEAD"))

    def test_main_with_a_base_skips_modules_that_added_nothing(self):
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps({"edited": ["VerifiedGarbage.C"]}))
        with mock.patch.object(check, "shake") as shake, \
                mock.patch.object(check, "new_public", return_value=set()):
            self.assertEqual(check.main([str(plan), "--base", "HEAD"]), 0)
            shake.assert_not_called()

    def test_the_modules_of_the_library(self):
        self.assertEqual(check.library_modules([
            "VerifiedGarbage.A", "VerifiedGarbage.Artifacts", "VerifiedGarbage.Legacy",
            "VerifiedGarbage.Gone", "Mathlib.Tactic"]), ["VerifiedGarbage.A"])

    def test_suggestions(self):
        text = ("/x/lean/VerifiedGarbage/C.lean:\n"
                "  remove #[public import VerifiedGarbage.B, import VerifiedGarbage.A]\n"
                "  add #[import VerifiedGarbage.B]\n"
                "/x/lean/VerifiedGarbage/A.lean:\n"
                "  add #[import Dep.X]\n")
        self.assertEqual(check.suggestions(text), {
            "/x/lean/VerifiedGarbage/C.lean": (["public import VerifiedGarbage.B", "import VerifiedGarbage.A"],
                                                ["import VerifiedGarbage.B"]),
            "/x/lean/VerifiedGarbage/A.lean": ([], ["import Dep.X"]),
        })

    def test_main_reads_the_plan(self):
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps({"edited": ["VerifiedGarbage.C", "VerifiedGarbage.Artifacts"]}))
        shaken = ("{}:\n  remove #[public import VerifiedGarbage.B]\n  add #[import VerifiedGarbage.B]\n"
                  .format(self.lean / "VerifiedGarbage/C.lean"))
        with mock.patch.object(check, "shake", return_value=shaken) as shake, \
                mock.patch.object(check, "dependency_roots", return_value=[self.lean, self.deps]):
            self.assertEqual(check.main([str(plan)]), 1)
            shake.assert_called_once_with(["VerifiedGarbage.C"])
            plan.write_text(json.dumps({"edited": []}))
            self.assertEqual(check.main([str(plan)]), 0)
            plan.write_text(json.dumps({}))
            self.assertEqual(check.main([str(plan)]), 0)


if __name__ == "__main__":
    unittest.main()
