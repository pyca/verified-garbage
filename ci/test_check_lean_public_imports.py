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

    def test_a_dependency_s_unused_import_when_asked(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport Dep.X\nimport Dep.Y -- shake: keep\n",
                    "deps/Dep/Y.lean": "module\n", "deps/Dep/Z.lean": "module\n"})
        self.graph = check.Graph([self.lean, self.deps], ("Dep",))
        rem = ["public import Dep.X"]
        f = str(self.lean / "VerifiedGarbage/B.lean")
        plan = check.analyze(["VerifiedGarbage.B"], {f: (rem, [])}, self.graph)
        self.assertEqual(plan.messages, ["lean/VerifiedGarbage/B.lean:4: `public import Dep.X`: "
                                         "VerifiedGarbage.B does not use this dependency's module: remove it"])
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.B", "remove_public", "Dep.X")])
        # A plain import, but not one marked to keep.
        [p] = self.problems("VerifiedGarbage.D", ["import Dep.X", "import Dep.Y"])
        self.assertEqual(p, "lean/VerifiedGarbage/D.lean:3: `import Dep.X`: "
                            "VerifiedGarbage.D does not use this dependency's module: remove it")
        # With a base, only those the change added.
        self.assertEqual(self.problems("VerifiedGarbage.D", ["import Dep.X"], plain={"VerifiedGarbage.D": set()}), [])
        # A narrower module of the dependency that shake adds comes in the same edit.
        f = str(self.lean / "VerifiedGarbage/D.lean")
        plan = check.analyze(["VerifiedGarbage.D"], {f: (["import Dep.X"], ["import Dep.Z"])}, self.graph)
        self.assertEqual(sorted(plan.edits), [check.Edit("VerifiedGarbage.D", "add", "Dep.Z"),
                                              check.Edit("VerifiedGarbage.D", "remove", "Dep.X")])
        self.assertIn("lean/VerifiedGarbage/D.lean: `import Dep.Z`: VerifiedGarbage.D uses this narrower "
                      "module of the dependency: import it instead", plan.messages)
        # Nothing to add when nothing is removed.
        plan = check.analyze(["VerifiedGarbage.D"], {f: ([], ["import Dep.Z"])}, self.graph)
        self.assertEqual(plan.edits, [])
        # Not of another dependency, or one shake does not find unused.
        self.graph = check.Graph([self.lean, self.deps], ("Other",))
        self.assertEqual(self.problems("VerifiedGarbage.D", ["import Dep.X"]), [])
        self.graph = check.Graph([self.lean, self.deps], ("Dep",))
        self.assertEqual(self.problems("VerifiedGarbage.D", []), [])
        # A prefix names whole components: `De` is not `Dep`.
        self.graph = check.Graph([self.lean, self.deps], ("De",))
        self.assertEqual(self.problems("VerifiedGarbage.D", ["import Dep.X"]), [])

    def test_fix_removes_a_dependency_s_import(self):
        self.graph = check.Graph([self.lean, self.deps], ("Dep",))
        f = str(self.lean / "VerifiedGarbage/B.lean")
        plan = check.analyze(["VerifiedGarbage.B"], {f: (["public import Dep.X"], [])}, self.graph)
        with mock.patch.object(check, "ROOT", self.lean.parent):
            done = check.fix(plan)
        self.assertEqual(done, ["lean/VerifiedGarbage/B.lean: remove_public Dep.X"])
        self.assertEqual((self.lean / "VerifiedGarbage/B.lean").read_text(),
                         "module\n\npublic import VerifiedGarbage.Seal\n")

    def test_a_dependency_s_removal_may_reorder_its_own_modules(self):
        # M imports Dep.Q, then Dep.R, which imports Dep.P and Dep.Q: removing
        # `import Dep.Q` loads Dep.P before Dep.Q, both opaque to the check.
        self.write({"lean/VerifiedGarbage/M.lean": "module\n\nimport Dep.Q\nimport Dep.R\n",
                    "lean/VerifiedGarbage/N.lean": "module\n\nimport VerifiedGarbage.M\n",
                    "deps/Dep/P.lean": "module\n", "deps/Dep/Q.lean": "module\n",
                    "deps/Dep/R.lean": "module\n\npublic import Dep.P\npublic import Dep.Q\n"})
        f = str(self.lean / "VerifiedGarbage/M.lean")
        library = ["VerifiedGarbage.M", "VerifiedGarbage.N"]
        uses = lambda mods, view: {}
        graph = check.Graph([self.lean, self.deps], ("Dep",))
        self.assertNotEqual(graph.load_order("VerifiedGarbage.M"),
                            check.Planned(graph, [check.Edit("VerifiedGarbage.M", "remove", "Dep.Q")])
                            .load_order("VerifiedGarbage.M"))
        plan = check.analyze(["VerifiedGarbage.M"], {f: (["import Dep.Q"], [])}, graph, uses=uses, library=library)
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.M", "remove", "Dep.Q")])
        self.assertEqual(plan.deferred, [])

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
        # C uses only Dep.X, which B passes on. With Dep.X and the effects
        # repaired explicitly, B has no remaining local use and can be removed.
        uses = lambda mods, view: {"VerifiedGarbage.C": {"Dep.X"}} if view == "public" else {}
        [p, _keep] = self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"],
                                   ["import VerifiedGarbage.B"], uses=uses)
        self.assertIn("remove it, import publicly itself what it used through it: "
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
        self.assertIn(("private", ["VerifiedGarbage.D", "VerifiedGarbage.E"]), seen)

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
                    "module\n\npublic import VerifiedGarbage.B\npublic import VerifiedGarbage.A\n"
                    "meta import VerifiedGarbage.B\n"})
        with mock.patch.object(check, "ROOT", root):
            self.assertEqual(check.new_public("VerifiedGarbage.C", "HEAD"), {"VerifiedGarbage.A"})
            self.assertIsNone(check.new_public("VerifiedGarbage.C", None))
            self.assertIsNone(check.new_public("VerifiedGarbage.New", "HEAD"))
            self.assertEqual(check.new_meta("VerifiedGarbage.C", "HEAD"), {"VerifiedGarbage.B"})
            self.assertEqual(check.new_plain("VerifiedGarbage.C", "HEAD"), set())

    def test_main_with_a_base_skips_modules_that_added_nothing(self):
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps({"edited": ["VerifiedGarbage.C"]}))
        with mock.patch.object(check, "shake") as shake, \
                mock.patch.object(check, "new_public", return_value=set()), \
                mock.patch.object(check, "new_plain", return_value=set()), \
                mock.patch.object(check, "new_meta", return_value=set()):
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

    def test_removals_do_not_justify_each_other(self):
        # F imports A and B; both pass on Seal, whose declaration `sealed` F names.
        # Each alone is redundant given the other; removing both would lose Seal.
        self.write({"lean/VerifiedGarbage/F.lean": "module\n\nimport VerifiedGarbage.A\nimport VerifiedGarbage.B\n"
                                                    "\nexample : True := by simp [sealed]\n"})
        self.graph = check.Graph([self.lean, self.deps])
        names = {"VerifiedGarbage.Seal": {"VG.sealed"}}
        uses = lambda mods, view: {m: names.get(m, set()) for m in mods} if view == "names" else {}
        # Seal has side effects, so make it a plain module for this test.
        self.write({"lean/VerifiedGarbage/Seal.lean": "module\n\ntheorem sealed : True := trivial\n"})
        self.graph = check.Graph([self.lean, self.deps])
        findings = self.problems("VerifiedGarbage.F", ["import VerifiedGarbage.A", "import VerifiedGarbage.B"], uses=uses)
        self.assertEqual(len(findings), 1)
        self.assertIn("`import VerifiedGarbage.A`", findings[0])

    def test_an_opened_namespace_keeps_its_import(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\n\npublic import VerifiedGarbage.B\nimport VerifiedGarbage.A\n"
                                                    "\nopen VG.Impl.Thing\n"})
        self.graph = check.Graph([self.lean, self.deps])
        names = {"VerifiedGarbage.A": {"VG.Impl.Thing.x"}}
        uses = lambda mods, view: {m: names.get(m, set()) for m in mods} if view == "names" else {}
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"], uses=uses), [])

    def test_fix_undoes_what_does_not_build(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport VerifiedGarbage.C\n"})
        found = check.Plan(edits=[
            check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A"),
            check.Edit("VerifiedGarbage.B", "demote", "Dep.X"),
        ])
        before = (self.lean / "VerifiedGarbage/C.lean").read_text()
        # D, which imports C, fails with C's change; B builds.
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", side_effect=[set(), {"VerifiedGarbage.D"}, set()]):
            kept, undone = check.fix_and_verify(found, ["VerifiedGarbage.B", "VerifiedGarbage.C", "VerifiedGarbage.D"])
        self.assertEqual(undone, ["VerifiedGarbage.C"])
        self.assertEqual((self.lean / "VerifiedGarbage/C.lean").read_text(), before)
        self.assertIn("import Dep.X\n", (self.lean / "VerifiedGarbage/B.lean").read_text())
        self.assertEqual(kept, ["lean/VerifiedGarbage/B.lean: demote Dep.X"])

    def test_fix(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\n\nimport VerifiedGarbage.C\n\n#guard true\n"})
        found = check.Plan(edits=[
            check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.B"),
            check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A"),
            check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.Seal"),
        ])
        with mock.patch.object(check, "ROOT", self.lean.parent):
            done = check.fix(found)
        self.assertEqual((self.lean / "VerifiedGarbage/C.lean").read_text(), "module\n\nimport VerifiedGarbage.B\n")
        # The editor applies exactly the planned phase; it does not invent a
        # meta import merely because an unrelated evaluation appears in D.
        self.assertEqual((self.lean / "VerifiedGarbage/D.lean").read_text(),
                         "module\n\nimport VerifiedGarbage.C\nimport VerifiedGarbage.Seal\n"
                         "\n#guard true\n")
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

    def test_relative_shake_paths_are_resolved_from_lean(self):
        plan = check.analyze(["VerifiedGarbage.C"],
                             {"VerifiedGarbage/C.lean": (["public import VerifiedGarbage.B"], [])}, self.graph)
        self.assertIn(check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.B"), plan.edits)

    def test_unrecognized_shake_failure_is_not_no_suggestions(self):
        def killed(args, cwd, log, attempt, timeout):
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text("killed\n")
            attempt.returncode = 137
            return attempt
        with mock.patch.object(check.lean_import_build, "command", side_effect=killed):
            with self.assertRaisesRegex(SystemExit, "exit 137"):
                check.shake(["VerifiedGarbage.C"], built=True)

    def test_shakes_suggestion_exit_is_valid_analysis_but_not_a_verified_build(self):
        output = f"{check.graph_path('VerifiedGarbage.C')}:\n  remove #[import VerifiedGarbage.A]\n"
        def suggested(args, cwd, log, attempt, timeout):
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text(output)
            attempt.returncode = 1
            return attempt
        with mock.patch.object(check.lean_import_build, "command", side_effect=suggested):
            self.assertEqual(check.shake(["VerifiedGarbage.C"], built=True), output)
        record, = (self.lean / ".lake/import-analysis").glob("*-shake.json")
        outcome = json.loads(record.read_text())
        self.assertTrue(outcome["valid_suggestions"])
        self.assertEqual(outcome["returncode"], 1)
        self.assertFalse(outcome["succeeded"])

    def test_a_cyclic_snapshot_graph_fails_instead_of_hanging(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\npublic import VerifiedGarbage.B\n",
                    "lean/VerifiedGarbage/B.lean": "module\npublic import VerifiedGarbage.A\n"})
        with self.assertRaisesRegex(ValueError, "cyclic"):
            check.Graph([self.lean]).passes("VerifiedGarbage.A")

    def test_downstream_source_uses_receive_repairs(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                    "lean/VerifiedGarbage/C.lean": "module\npublic import VerifiedGarbage.A\n",
                    "lean/VerifiedGarbage/D.lean": "module\nimport VerifiedGarbage.C\nopen VG.A\n"})
        graph = check.Graph([self.lean])
        def uses(mods, view):
            return {m: ({"VG.A.lemma"} if view == "names" else {"VG", "VG.A"} if view == "namespaces" else set())
                    if m == "VerifiedGarbage.A" else set() for m in mods}
        plan = check.analyze(["VerifiedGarbage.C"],
                             {str(check.graph_path("VerifiedGarbage.C")): (["public import VerifiedGarbage.A"], [])},
                             graph, uses=uses, library=["VerifiedGarbage.C", "VerifiedGarbage.D"])
        self.assertIn(check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.A"), plan.edits)

    def test_header_and_reverse_index_agree_on_nested_copyright(self):
        text = "/- copyright\n /- nested -/\n continued\n-/\nmodule\n\nimport VerifiedGarbage.B -- why\n"
        self.write({"lean/VerifiedGarbage/C.lean": text})
        self.assertTrue(check.is_module(text))
        self.assertEqual(check.header(text), [("VerifiedGarbage.B", False, False, False)])
        self.assertEqual(check.header_imports(self.lean / "VerifiedGarbage/C.lean"), ["VerifiedGarbage.B"])

    def test_preservation_advice_is_executable(self):
        path = str(self.lean / "VerifiedGarbage/C.lean")
        plan = check.analyze(["VerifiedGarbage.C"], {path: (["public import VerifiedGarbage.B"], [])}, self.graph)
        self.assertIn(check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.Seal"), plan.edits)
        self.assertIn(check.Edit("VerifiedGarbage.C", "add_public", "Dep.X"), plan.edits)
        with mock.patch.object(check, "ROOT", self.lean.parent):
            check.fix(plan)
        after = check.Graph([self.lean, self.deps])
        self.assertIn("VerifiedGarbage.Seal", after.passes("VerifiedGarbage.C"))
        self.assertIn("Dep.X", after.passes("VerifiedGarbage.C"))

    def test_combined_diamond_losses_and_public_repairs(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\npublic import VerifiedGarbage.B\n",
                    "lean/VerifiedGarbage/C.lean": "module\npublic import VerifiedGarbage.B\n",
                    "lean/VerifiedGarbage/B.lean": "module\n",
                    "lean/VerifiedGarbage/D.lean": "module\nimport VerifiedGarbage.A\nimport VerifiedGarbage.C\n"})
        graph = check.Graph([self.lean])
        mods = ["VerifiedGarbage.A", "VerifiedGarbage.C"]
        shaken = {str(check.graph_path(m)): (["public import VerifiedGarbage.B"], []) for m in mods}
        uses = lambda ms, view: {m: {"VerifiedGarbage.B"} if m == "VerifiedGarbage.D" else set() for m in ms}
        plan = check.analyze(mods, shaken, graph, uses=uses, library=mods + ["VerifiedGarbage.D"])
        self.assertIn(check.Edit("VerifiedGarbage.D", "add_public", "VerifiedGarbage.B"), plan.edits)
        with mock.patch.object(check, "ROOT", self.lean.parent):
            check.fix(plan)
        self.assertIn("VerifiedGarbage.B", check.Graph([self.lean]).passes("VerifiedGarbage.D"))

    def test_keep_is_enforced_even_when_shake_suggests_removal(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\npublic import VerifiedGarbage.B -- shake: keep\n"})
        self.graph = check.Graph([self.lean, self.deps])
        self.assertEqual(self.problems("VerifiedGarbage.C", ["public import VerifiedGarbage.B"]), [])

    def test_private_path_does_not_replace_lost_public_visibility(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\npublic import VerifiedGarbage.B\n",
                    "lean/VerifiedGarbage/B.lean": "module\n",
                    "lean/VerifiedGarbage/D.lean": "module\npublic import VerifiedGarbage.A\nimport VerifiedGarbage.B\n"})
        graph = check.Graph([self.lean])
        uses = lambda ms, view: {m: {"VerifiedGarbage.B"} if m == "VerifiedGarbage.D" else set() for m in ms}
        plan = check.analyze(["VerifiedGarbage.A"],
                             {str(check.graph_path("VerifiedGarbage.A")): (["public import VerifiedGarbage.B"], [])},
                             graph, uses=uses, library=["VerifiedGarbage.A", "VerifiedGarbage.D"])
        self.assertIn(check.Edit("VerifiedGarbage.D", "add_public", "VerifiedGarbage.B"), plan.edits)

    def test_removal_preserves_transitive_effects(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.B\n"})
        self.graph = check.Graph([self.lean, self.deps])
        uses = lambda ms, view: {m: set() for m in ms}
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.B"], uses=uses), [])

    def test_declaration_evidence_can_veto_shake_removal(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                    "lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.A\n"})
        self.graph = check.Graph([self.lean])
        uses = lambda ms, view: {m: {"VerifiedGarbage.A"} if view == "private" else set() for m in ms}
        self.assertEqual(self.problems("VerifiedGarbage.C", ["import VerifiedGarbage.A"], uses=uses), [])

    def test_a_used_direct_import_stays_even_when_another_path_supplies_it(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                    "lean/VerifiedGarbage/B.lean": "module\npublic import VerifiedGarbage.A\n",
                    "lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.A\npublic import VerifiedGarbage.B\n"})
        graph = check.Graph([self.lean])
        uses = lambda ms, view: {m: {"VerifiedGarbage.A"} if view == "private" else set() for m in ms}
        plan = check.analyze(["VerifiedGarbage.C"],
                             {str(check.graph_path("VerifiedGarbage.C")): (["import VerifiedGarbage.A"], [])},
                             graph, uses=uses)
        self.assertNotIn(check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A"), plan.edits)
        direct = next(d for d in plan.decisions if d["dependency"] == "VerifiedGarbage.A")
        self.assertEqual(direct["reason"], "direct_dependency")

    def test_commented_demotion_and_duplicate_repairs(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\npublic import VerifiedGarbage.B -- why\n"})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.B"),
                                check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.A"),
                                check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.A")])
        with mock.patch.object(check, "ROOT", self.lean.parent):
            done = check.fix(plan)
        self.assertEqual(len(done), 2)
        self.assertEqual((self.lean / "VerifiedGarbage/C.lean").read_text(),
                         "module\nimport VerifiedGarbage.B -- why\npublic import VerifiedGarbage.A\n")

    def test_added_imports_stay_outside_multiline_header_comments(self):
        layouts = [
            "module\nimport VerifiedGarbage.B /- why\n  explanation -/\n#guard true\n",
            "module\nimport VerifiedGarbage.B /- why\n /- nested -/ explanation -/ #guard true\n",
            "module\nimport VerifiedGarbage.B /- why\n explanation -/ /-! module documentation -/\n#guard true\n",
            "module /- why\n explanation -/\n#guard true\n",
            "module\nprelude /- why\n explanation -/\n",
            "module\nimport VerifiedGarbage.B /- why\n explanation -/",
            "module\nimport VerifiedGarbage.B -- shake: keep\n/-! module documentation -/\n#guard true\n",
        ]
        for source in layouts:
            self.write({"lean/VerifiedGarbage/C.lean": source})
            plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.A"),
                                    check.Edit("VerifiedGarbage.C", "add_meta", "VerifiedGarbage.Seal")])
            with mock.patch.object(check, "ROOT", self.lean.parent):
                check.fix(plan)
            text = check.graph_path("VerifiedGarbage.C").read_text()
            self.assertEqual(set(check.header(text)), set(check.header(source)) | {
                ("VerifiedGarbage.A", True, False, False), ("VerifiedGarbage.Seal", False, True, False)})
            if "#guard true" in source:
                self.assertIn("#guard true", text)
                old = next(line.index("#guard true") for line in source.splitlines() if "#guard true" in line)
                new = next(line.index("#guard true") for line in text.splitlines() if "#guard true" in line)
                self.assertEqual(new, old)
            if "shake: keep" in source:
                self.assertIn("import VerifiedGarbage.B -- shake: keep", text)
            if "prelude" in source:
                self.assertLess(text.index("prelude"), text.index("public import"))

    def test_added_import_refuses_an_unterminated_header_comment(self):
        source = "module\nimport VerifiedGarbage.B /- unfinished\n"
        self.write({"lean/VerifiedGarbage/C.lean": source})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "add", "VerifiedGarbage.A")])
        with self.assertRaisesRegex(ValueError, "unterminated"):
            check.render(plan)
        self.assertEqual(check.graph_path("VerifiedGarbage.C").read_text(), source)

    def test_public_repair_promotes_commented_plain_import(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.B -- why\n#guard true\n"})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.B")])
        with mock.patch.object(check, "ROOT", self.lean.parent):
            check.fix(plan)
        text = (self.lean / "VerifiedGarbage/C.lean").read_text()
        self.assertIn("public import VerifiedGarbage.B -- why", text)
        self.assertEqual(text.count("meta import VerifiedGarbage.B"), 0)

    def test_public_repair_preserves_a_pinned_private_occurrence(self):
        for phase, action in (("", "add_public"), ("meta ", "add_public_meta")):
            for extra in ("", f"{phase}import VerifiedGarbage.B -- unpinned\n"):
                pinned = f"{phase}import VerifiedGarbage.B -- shake: keep\n"
                self.write({"lean/VerifiedGarbage/C.lean": "module\n" + pinned + extra})
                plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", action, "VerifiedGarbage.B")])
                with mock.patch.object(check, "ROOT", self.lean.parent):
                    check.fix(plan)
                text = check.graph_path("VerifiedGarbage.C").read_text()
                self.assertIn("\n" + pinned, text)
                self.assertIn(f"\npublic {phase}import VerifiedGarbage.B", text)
                self.assertEqual(text.count("import VerifiedGarbage.B"), 2)

    def test_keep_all_refuses_stale_or_manually_constructed_plans(self):
        original = "module -- shake: keep-all\npublic import VerifiedGarbage.B\n"
        self.write({"lean/VerifiedGarbage/C.lean": original})
        for action in ("demote", "remove_public", "add", "add_public_meta"):
            plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", action, "VerifiedGarbage.B")])
            with self.assertRaisesRegex(ValueError, "keep-all"):
                check.render(plan)
            self.assertEqual(check.graph_path("VerifiedGarbage.C").read_text(), original)

    def test_keep_all_downstream_repair_defers_only_its_upstream_boundary(self):
        self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                    "lean/VerifiedGarbage/C.lean": "module\npublic import VerifiedGarbage.A\n",
                    "lean/VerifiedGarbage/D.lean": "module -- shake: keep-all\nimport VerifiedGarbage.C\n",
                    "lean/VerifiedGarbage/E.lean": "module\nimport VerifiedGarbage.A\n"})
        def uses(mods, view):
            return {m: {"VerifiedGarbage.A"} if m == "VerifiedGarbage.D" and view == "private"
                    else set() for m in mods}
        plan = check.analyze(["VerifiedGarbage.C", "VerifiedGarbage.E"], {
            str(check.graph_path("VerifiedGarbage.C")): (["public import VerifiedGarbage.A"], []),
            str(check.graph_path("VerifiedGarbage.E")): (["import VerifiedGarbage.A"], []),
        }, check.Graph([self.lean]), uses=uses,
            library=["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"])
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.E", "remove", "VerifiedGarbage.A")])
        self.assertFalse(plan.blocked)
        self.assertEqual(plan.deferred[0]["kept_importers"], ["VerifiedGarbage.D"])

    def meta_plan(self, imports, evidence=None, body=""):
        self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                    "lean/VerifiedGarbage/B.lean": "module\npublic import VerifiedGarbage.A\n",
                    "lean/VerifiedGarbage/C.lean": "module\n" + imports + body})
        uses = lambda mods, view: {m: set((evidence or {}).get(view, {}).get(m, [])) for m in mods}
        return check.analyze(["VerifiedGarbage.C"],
                             {str(check.graph_path("VerifiedGarbage.C")): (["meta import VerifiedGarbage.B"], [])},
                             check.Graph([self.lean]), uses=uses)

    def test_unused_private_meta_import_has_a_distinct_operation(self):
        plan = self.meta_plan("import VerifiedGarbage.B\nmeta import VerifiedGarbage.B -- execution\n"
                              "public meta import VerifiedGarbage.A\nmeta import all VerifiedGarbage.B\n")
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.C", "remove_meta", "VerifiedGarbage.B")])
        with mock.patch.object(check, "ROOT", self.lean.parent):
            check.fix(plan)
        text = check.graph_path("VerifiedGarbage.C").read_text()
        self.assertIn("\nimport VerifiedGarbage.B\n", text)
        self.assertIn("-- execution", text)
        self.assertIn("public meta import VerifiedGarbage.A", text)
        self.assertIn("meta import all VerifiedGarbage.B", text)
        self.assertNotIn("\nmeta import VerifiedGarbage.B", text)

    def test_private_meta_removal_respects_the_selected_diff(self):
        self.meta_plan("meta import VerifiedGarbage.B\n")
        uses = lambda mods, view: {m: set() for m in mods}
        plan = check.analyze(["VerifiedGarbage.C"],
                             {str(check.graph_path("VerifiedGarbage.C")): (["meta import VerifiedGarbage.B"], [])},
                             check.Graph([self.lean]), uses=uses, meta_plain={"VerifiedGarbage.C": set()})
        self.assertFalse(plan.edits)
        self.assertEqual(plan.decisions[0]["reason"], "outside_selected_diff")

    def test_private_meta_dependencies_and_resolved_source_uses_are_retained(self):
        for view in ("meta_private", "references"):
            for dep in ("VerifiedGarbage.B", "VerifiedGarbage.A"):
                plan = self.meta_plan("meta import VerifiedGarbage.B\n", {view: {"VerifiedGarbage.C": [dep]}})
                self.assertFalse(plan.edits, (view, dep))
                decision = next(d for d in plan.decisions if d["dependency"] == "VerifiedGarbage.B")
                self.assertEqual(decision["status"], "retained")
                self.assertTrue(decision["meta"])

    def test_private_meta_keep_markers_and_unknown_effects_are_retained(self):
        for imports in ("meta import VerifiedGarbage.B -- shake: keep\n",
                        "meta import VerifiedGarbage.B\n"):
            plan = self.meta_plan(imports)
            if "keep" in imports:
                self.assertFalse(plan.edits)
            else:
                self.write({"lean/VerifiedGarbage/A.lean": "module\nsyntax \"example\" : term\n"})
                uses = lambda mods, view: {m: set() for m in mods}
                plan = check.analyze(["VerifiedGarbage.C"],
                                     {str(check.graph_path("VerifiedGarbage.C")): (["meta import VerifiedGarbage.B"], [])},
                                     check.Graph([self.lean]), uses=uses)
                self.assertFalse(plan.edits)
                self.assertEqual(plan.decisions[0]["reason"], "opaque_private_execution_effects")

    def test_private_meta_only_namespace_provider_is_retained(self):
        plan = self.meta_plan("meta import VerifiedGarbage.B\n",
                              {"namespaces": {"VerifiedGarbage.A": ["Fixture"]}}, "open Fixture\n")
        self.assertFalse(plan.edits)
        self.assertEqual(plan.decisions[0]["reason"], "source_dependency")

    def test_generated_transitive_instances_guard_private_meta_removal(self):
        plan = self.meta_plan("meta import VerifiedGarbage.B\n", {
            "effects": {"VerifiedGarbage.A": [check.INSTANCE_EXTENSION]}})
        self.assertFalse(plan.edits)
        self.assertEqual(plan.decisions[0]["reason"], "opaque_private_execution_effects")

    def test_unfamiliar_registry_metadata_preserves_its_provider(self):
        for registry in ("default", "User.CustomSearchRules"):
            plan = self.meta_plan("meta import VerifiedGarbage.B\n", {
                "effects": {"VerifiedGarbage.B": [registry]}})
            self.assertFalse(plan.edits)
            self.assertEqual(plan.decisions[0]["evidence"]["extensions"], [registry])

    def test_structural_metadata_does_not_block_narrowing(self):
        plan = self.meta_plan("meta import VerifiedGarbage.B\n", {
            "effects": {"VerifiedGarbage.B": ["Lean.IR.declMapExt", "Lean.Compiler.LCNF.baseExt"]}})
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.C", "remove_meta", "VerifiedGarbage.B")])

    def test_kept_import_all_consumer_defers_ordinary_and_meta_private_removals(self):
        for phase, view in (("", "private"), ("meta ", "meta_private")):
            self.write({"lean/VerifiedGarbage/A.lean": "module\n",
                        "lean/VerifiedGarbage/C.lean": f"module\n{phase}import VerifiedGarbage.A\n",
                        "lean/VerifiedGarbage/D.lean": "module -- shake: keep-all\nimport all VerifiedGarbage.C\n",
                        "lean/VerifiedGarbage/E.lean": "module\nimport VerifiedGarbage.A\n"})
            uses = lambda mods, v: {m: {"VerifiedGarbage.A"} if m == "VerifiedGarbage.D" and v == view
                                   else set() for m in mods}
            plan = check.analyze(["VerifiedGarbage.C", "VerifiedGarbage.E"], {
                str(check.graph_path("VerifiedGarbage.C")): ([f"{phase}import VerifiedGarbage.A"], []),
                str(check.graph_path("VerifiedGarbage.E")): (["import VerifiedGarbage.A"], []),
            }, check.Graph([self.lean]), uses=uses,
                library=["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"])
            self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.E", "remove", "VerifiedGarbage.A")])
            self.assertEqual(plan.deferred[0]["kept_importers"], ["VerifiedGarbage.D"])

    def test_demotion_selects_every_public_occurrence_after_a_private_one(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.B -- proof\n"
                    "public import VerifiedGarbage.B -- interface\npublic import VerifiedGarbage.B -- duplicate\n"
                    "public meta import VerifiedGarbage.B -- tools\n"})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.B")])
        before = check.Graph([self.lean, self.deps])
        expected = check.Planned(before, plan.edits)
        with mock.patch.object(check, "ROOT", self.lean.parent):
            check.fix(plan)
        actual = check.Graph([self.lean, self.deps])
        self.assertEqual(set(actual.imports("VerifiedGarbage.C")), set(expected.imports("VerifiedGarbage.C")))
        self.assertNotIn("public import VerifiedGarbage.B", check.graph_path("VerifiedGarbage.C").read_text())
        self.assertIn("-- interface", check.graph_path("VerifiedGarbage.C").read_text())

    def test_removal_selects_only_the_requested_visibility_and_preserves_all_and_meta(self):
        source = "module\nimport VerifiedGarbage.B\npublic import VerifiedGarbage.B\nimport all VerifiedGarbage.B\nmeta import VerifiedGarbage.B\n"
        for action in ("remove", "remove_public"):
            self.write({"lean/VerifiedGarbage/C.lean": source})
            plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", action, "VerifiedGarbage.B")])
            expected = check.Planned(check.Graph([self.lean, self.deps]), plan.edits)
            with mock.patch.object(check, "ROOT", self.lean.parent):
                check.fix(plan)
            actual = check.Graph([self.lean, self.deps])
            self.assertEqual(set(actual.imports("VerifiedGarbage.C")), set(expected.imports("VerifiedGarbage.C")))

    def test_early_validation_failure_has_a_durable_abort_record(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.Missing")])
        audit = {}
        with mock.patch.object(check, "build_failures") as build:
            with self.assertRaisesRegex(ValueError, "no longer present"):
                check.fix_and_verify(plan, ["VerifiedGarbage.C"], audit=audit)
        build.assert_not_called()
        self.assertEqual(json.loads(pathlib.Path(audit["manifest"]).read_text())["status"], "aborted")

    def test_explanation_identifies_the_effect_that_prevents_removal(self):
        self.write({"lean/VerifiedGarbage/C.lean": "module\nimport VerifiedGarbage.B\n"})
        plan = check.analyze(["VerifiedGarbage.C"],
                             {str(check.graph_path("VerifiedGarbage.C")): (["import VerifiedGarbage.B"], [])},
                             check.Graph([self.lean, self.deps]), uses=lambda ms, view: {m: set() for m in ms})
        decision, = plan.decisions
        self.assertEqual(decision["status"], "retained")
        self.assertEqual(decision["reason"], "opaque_transitive_effects")
        self.assertEqual(decision["evidence"]["modules"], ["Dep.X", "VerifiedGarbage.Seal"])

    def test_a_failing_baseline_does_not_apply_or_restore_sources(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A")])
        path = self.lean / "VerifiedGarbage/C.lean"
        original = path.read_text()
        audit = {}
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", return_value={"VerifiedGarbage.C"}), \
                mock.patch.object(check, "fix") as fix:
            with self.assertRaisesRegex(RuntimeError, "baseline does not build"):
                check.fix_and_verify(plan, ["VerifiedGarbage.C"], audit=audit)
        fix.assert_not_called()
        self.assertEqual(path.read_text(), original)
        self.assertFalse(audit["build_verified"])

    def test_exhausted_attempt_budget_restores_the_whole_batch(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A"),
                                check.Edit("VerifiedGarbage.A", "demote", "VerifiedGarbage.B")])
        saved = {p: p.read_text() for p in plan.paths()}
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", side_effect=[set(), {"VerifiedGarbage.C"}]):
            with self.assertRaisesRegex(RuntimeError, "attempt budget"):
                check.fix_and_verify(plan, ["VerifiedGarbage.A", "VerifiedGarbage.C"], max_attempts=1)
        self.assertEqual({p: p.read_text() for p in saved}, saved)

    def test_verification_only_succeeds_after_every_chunk_passes(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\nimport VerifiedGarbage.C\n",
                    "lean/VerifiedGarbage/E.lean": "module\nimport VerifiedGarbage.C\n"})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A")])
        audit = {}
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", return_value=set()) as build:
            kept, undone = check.fix_and_verify(plan, ["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"],
                                                verify_batch=2, audit=audit)
        self.assertTrue(kept)
        self.assertFalse(undone)
        self.assertTrue(audit["build_verified"])
        self.assertEqual([(call.args[0], call.kwargs["phase"]) for call in build.call_args_list], [
            (["VerifiedGarbage.C", "VerifiedGarbage.D"], "baseline"), (["VerifiedGarbage.E"], "baseline"),
            (["VerifiedGarbage.C", "VerifiedGarbage.D"], "verify"), (["VerifiedGarbage.E"], "verify")])

    def test_a_failing_chunk_stops_the_pass_and_restores_its_cause(self):
        self.write({"lean/VerifiedGarbage/D.lean": "module\nimport VerifiedGarbage.C\n",
                    "lean/VerifiedGarbage/E.lean": "module\nimport VerifiedGarbage.C\n"})
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A")])
        before = check.graph_path("VerifiedGarbage.C").read_text()
        audit = {}
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", side_effect=[set(), set(), {"VerifiedGarbage.D"}]) as build:
            kept, undone = check.fix_and_verify(plan, ["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"],
                                                verify_batch=2, audit=audit)
        self.assertFalse(kept)
        self.assertEqual(undone, ["VerifiedGarbage.C"])
        self.assertEqual(build.call_count, 3)
        self.assertFalse(audit["build_verified"])
        self.assertEqual(check.graph_path("VerifiedGarbage.C").read_text(), before)

    def test_protected_repair_blocks_its_demotion(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "demote", "VerifiedGarbage.B"),
                                check.Edit("VerifiedGarbage.Artifacts.X", "add", "VerifiedGarbage.B")])
        plan.exclude_reviewed()
        self.assertEqual(len(plan.edits), 2)
        self.assertTrue(plan.blocked)

    def test_build_failure_without_parseable_output_is_not_success(self):
        def killed(mods, cwd, log, phase, timeout, attempt):
            attempt.returncode = 137
            return attempt
        with mock.patch.object(check, "BUILD_LOG", self.lean / "build.log"), \
                mock.patch.object(check.lean_import_build, "build", side_effect=killed):
            with self.assertRaisesRegex(RuntimeError, "137"):
                check.build_failures(["VerifiedGarbage.C"])

    def test_a_reader_failure_is_durable_and_never_empty_evidence(self):
        def killed(args, cwd, log, attempt, timeout):
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text("reader was killed\n")
            attempt.returncode = -9
            return attempt
        with mock.patch.object(check.lean_import_build, "command", side_effect=killed):
            with self.assertRaisesRegex(RuntimeError, "reader exited -9"):
                check.module_evidence(["VerifiedGarbage.C"], 5)
        records = list((self.lean / ".lake/import-analysis").glob("*-reader-*.json"))
        self.assertEqual(len(records), 1)
        self.assertFalse(json.loads(records[0].read_text())["succeeded"])

    def test_zero_exit_with_partial_reader_output_is_recorded_as_a_failure(self):
        def incomplete(args, cwd, log, attempt, timeout):
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text('{}\n')
            attempt.returncode = 0
            return attempt
        with mock.patch.object(check.lean_import_build, "command", side_effect=incomplete):
            with self.assertRaisesRegex(ValueError, "incomplete declaration evidence"):
                check.module_evidence(["VerifiedGarbage.C"], 5)
        record, = (self.lean / ".lake/import-analysis").glob("*-reader-*.json")
        self.assertFalse(json.loads(record.read_text())["succeeded"])

    def test_verification_exception_restores_every_edited_source(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.A")])
        path = self.lean / "VerifiedGarbage/C.lean"
        before = path.read_text()
        with mock.patch.object(check, "ROOT", self.lean.parent), \
                mock.patch.object(check, "build_failures", side_effect=[set(), KeyboardInterrupt]):
            with self.assertRaises(KeyboardInterrupt):
                check.fix_and_verify(plan, ["VerifiedGarbage.C"])
        self.assertEqual(path.read_text(), before)

    def test_editor_validates_every_operation_before_writing(self):
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.A", "demote", "VerifiedGarbage.B"),
                                check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.Missing")])
        path = self.lean / "VerifiedGarbage/A.lean"
        before = path.read_text()
        with mock.patch.object(check, "ROOT", self.lean.parent):
            with self.assertRaisesRegex(ValueError, "no longer present"):
                check.fix(plan)
        self.assertEqual(path.read_text(), before)

    def test_main_reads_the_plan(self):
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps({"edited": ["VerifiedGarbage.C", "VerifiedGarbage.Artifacts"]}))
        shaken = ("{}:\n  remove #[public import VerifiedGarbage.B]\n  add #[import VerifiedGarbage.B]\n"
                  .format(self.lean / "VerifiedGarbage/C.lean"))
        with mock.patch.object(check, "shake", return_value=shaken) as shake, \
                mock.patch.object(check, "build_modules"), \
                mock.patch.object(check, "module_evidence", side_effect=lambda ms, *args: {
                    m: {v: set() for v in check.DECLARATION_VIEWS} for m in ms}), \
                mock.patch.object(check, "module_uses", side_effect=lambda ms, view: {m: set() for m in ms}), \
                mock.patch.object(check, "dependency_roots", return_value=[self.lean, self.deps]):
            self.assertEqual(check.main([str(plan)]), 1)
            shake.assert_called_once_with(["VerifiedGarbage.C"], built=True, timeout=None)
            plan.write_text(json.dumps({"edited": []}))
            self.assertEqual(check.main([str(plan)]), 0)
            plan.write_text(json.dumps({}))
            self.assertEqual(check.main([str(plan)]), 0)


if __name__ == "__main__":
    unittest.main()
