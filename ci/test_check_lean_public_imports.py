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

    def problems(self, mod, rem, add=(), **kw):
        f = str(self.lean / (mod.replace(".", "/") + ".lean"))
        return check.problems([mod], {f: (list(rem), list(add))}, self.graph, **kw)

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

    def test_meta_imports_are_not_asked_about(self):
        self.assertEqual(self.problems("VerifiedGarbage.C", ["public meta import VerifiedGarbage.B"]), [])

    def test_an_unused_plain_import(self):
        [p] = self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"])
        self.assertEqual(p, "lean/VerifiedGarbage/C.lean:4: `import VerifiedGarbage.A`: "
                            "VerifiedGarbage.C does not use it: remove it")
        # Only those the change added, with a base.
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"],
                                       plain={"VerifiedGarbage.C": set()}), [])
        # Not one shake replaces by itself, or a module with side effects.
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"],
                                       ["import VerifiedGarbage.A"]), [])

    def test_a_proof_inside_an_exposed_definition_is_a_public_use(self):
        # Lean checks what the proofs of C's exposed definitions use as public.
        # C uses B itself there: it keeps `public import B`.
        uses = lambda mods, view: {"VerifiedGarbage.C": {"VerifiedGarbage.B"}} if view == "public" else {}
        self.assertEqual(self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"],
                                       ["import VerifiedGarbage.B"], uses=uses), [])
        # C uses only Dep.X, which B passes on: B becomes a plain import, and C
        # imports Dep.X publicly itself.
        uses = lambda mods, view: {"VerifiedGarbage.C": {"Dep.X"}} if view == "public" else {}
        [p, _keep] = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"],
                                   ["import VerifiedGarbage.B"], uses=uses)
        self.assertIn("make it `import VerifiedGarbage.B`, import publicly itself what it used through it: "
                      "`public import Dep.X`", p)
        # A use of what does not come through B (A, a plain import) needs nothing.
        uses = lambda mods, view: {"VerifiedGarbage.C": {"VerifiedGarbage.A"}} if view == "public" else {}
        [p, _keep] = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"],
                                   ["import VerifiedGarbage.B"], uses=uses)
        self.assertNotIn("import publicly itself", p)

    def test_the_importers_that_used_what_it_passed_on(self):
        # D imports C, which passes on B; D uses B, E does not.
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport VerifiedGarbage.C\n",
                    "lean/VerifiedGarbage/E.lean": "module\n\nimport VerifiedGarbage.C\n"})
        self.graph = check.Graph([self.lean, self.deps])
        seen = []
        def uses(mods, view):
            seen.append((view, sorted(mods)))
            return {"VerifiedGarbage.D": {"VerifiedGarbage.B"}} if view == "private" else {}
        [p, _] = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"], ["import VerifiedGarbage.B"],
                               uses=uses, library=["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"])
        self.assertIn("import what it passed on where it is used: VerifiedGarbage.D uses VerifiedGarbage.B", p)
        self.assertNotIn("VerifiedGarbage.E", p)
        # Only the modules that lose something are loaded.
        self.assertEqual(seen[-1], ("private", ["VerifiedGarbage.D", "VerifiedGarbage.E"]))

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
                mock.patch.object(check, "new_public", return_value=set()), \
                mock.patch.object(check, "new_plain", return_value=set()):
            self.assertEqual(check.main([str(plan), "--base", "HEAD"]), 0)
            shake.assert_not_called()

    def test_an_import_whose_declaration_the_source_names_stays(self):
        # Shake finds no use of A in C's `.olean`, but C's tactic names `a_lemma`.
        self.write({"lean/VerifiedGarbage/C.lean": "module\n\npublic import VerifiedGarbage.B\nimport VerifiedGarbage.A\n"
                                                    "\nexample : True := by simp [a_lemma]\n"})
        self.graph = check.Graph([self.lean, self.deps])
        names = {"VerifiedGarbage.A": {"VG.A.a_lemma"}}
        uses = lambda mods, view: {m: names.get(m, set()) for m in mods} if view == "names" else {}
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"], uses=uses), [])
        names = {"VerifiedGarbage.A": {"VG.A.other"}}
        [p] = self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"], uses=uses)
        self.assertIn("does not use it: remove it", p)

    def test_fix_undoes_what_does_not_build(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport VerifiedGarbage.C\n"})
        found = ["lean/VerifiedGarbage/C.lean:4: `import VerifiedGarbage.A`: VerifiedGarbage.C does not use it: remove it",
                 "lean/VerifiedGarbage/B.lean:4: `public import Dep.X`: VerifiedGarbage.B uses it only privately: "
                 "make it `import Dep.X`, and import it where the modules importing VerifiedGarbage.B use it"]
        before = (self.lean / "VerifiedGarbage/C.lean").read_text()
        # D, which imports C, fails with C's change; B builds.
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", side_effect=[{"VerifiedGarbage.D"}, set()]):
            kept, undone = check.fix_and_verify(found, ["VerifiedGarbage.B", "VerifiedGarbage.C", "VerifiedGarbage.D"])
        self.assertEqual(undone, ["VerifiedGarbage.C"])
        self.assertEqual((self.lean / "VerifiedGarbage/C.lean").read_text(), before)
        self.assertIn("import Dep.X\n", (self.lean / "VerifiedGarbage/B.lean").read_text())
        self.assertEqual(kept, ["lean/VerifiedGarbage/B.lean: demote Dep.X"])

    def test_fix(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport VerifiedGarbage.C\n\n#guard true\n"})
        found = [
            "lean/VerifiedGarbage/C.lean:3: `public import VerifiedGarbage.B`: VerifiedGarbage.C uses it only "
            "privately: make it `import VerifiedGarbage.B`, and import what it passed on where it is used: "
            "VerifiedGarbage.D uses VerifiedGarbage.Seal",
            "lean/VerifiedGarbage/C.lean:4: `import VerifiedGarbage.A`: VerifiedGarbage.C does not use it: remove it",
        ]
        with mock.patch.object(check, "ROOT", self.lean.parent):
            done = check.fix(found)
        self.assertEqual((self.lean / "VerifiedGarbage/C.lean").read_text(), "module\n\nimport VerifiedGarbage.B\n")
        # D evaluates code: it imports Seal both ways.
        self.assertEqual((self.lean / "VerifiedGarbage/D.lean").read_text(),
                         "module\n\nimport VerifiedGarbage.C\nimport VerifiedGarbage.Seal\n"
                         "meta import VerifiedGarbage.Seal\n\n#guard true\n")
        self.assertEqual(len(done), 3)

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
                mock.patch.object(check, "module_uses", return_value={}), \
                mock.patch.object(check, "dependency_roots", return_value=[self.lean, self.deps]):
            self.assertEqual(check.main([str(plan)]), 1)
            shake.assert_called_once_with(["VerifiedGarbage.C"])
            plan.write_text(json.dumps({"edited": []}))
            self.assertEqual(check.main([str(plan)]), 0)
            plan.write_text(json.dumps({}))
            self.assertEqual(check.main([str(plan)]), 0)


if __name__ == "__main__":
    unittest.main()
