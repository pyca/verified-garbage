"""Small compiled semantic tests; no Lake build or cryptographic proofs.

Run with the repository's Lean toolchain installed. Without Lean these are
explicitly skipped; the planner/replay tests still run on plain Python.
The optional Aesop case also needs the project's compiled package cache.
"""

import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

import check_lean_public_imports as check
import check_lean_imports as import_discipline
import lean_import_replay as replay

HELPER = pathlib.Path(check.__file__).with_name("lean_module_uses.lean")
LEAN = shutil.which("lean")
REPO_LEAN = check.LEAN


@unittest.skipUnless(LEAN, "Lean toolchain is not installed")
class LeanImports(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.env = dict(os.environ, LEAN_PATH=str(self.root))
        self.declaration_cache = {}
        self.write("B", "public import Init\n\n@[expose] public section\n"
                         "namespace Fixture\ntheorem witness : True := True.intro\n"
                         "theorem derive {n : Nat} (_ : n = 0) : True := True.intro\nend Fixture\n")
        self.compile("B")

    def run_lean(self, *args):
        out = subprocess.run([LEAN, *map(str, args)], cwd=REPO_LEAN, env=self.env,
                             capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        return out.stdout

    def write(self, name, source):
        self.write_module("VerifiedGarbage." + name, source)

    def write_module(self, mod, source):
        path = self.root.joinpath(*mod.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("module\n\n" + source)

    def compile(self, name):
        self.compile_module("VerifiedGarbage." + name)

    def compile_module(self, mod):
        path = self.root.joinpath(*mod.split(".")).with_suffix(".lean")
        self.run_lean(f"--root={self.root}", "-o", path.with_suffix(".olean"), "-i", path.with_suffix(".ilean"), path)
        self.declaration_cache.clear()

    def uses(self, mods, view):
        if view in ("references", "namespaces"):
            result = {}
            for m in mods:
                source = self.root.joinpath(*m.split(".")).with_suffix(".lean")
                data = check.lean_source_evidence.read(self.root, m, check.header(source.read_text()), build=self.root)
                result[m] = (check.lean_source_evidence.references(data) if view == "references"
                             else check.lean_source_evidence.namespaces(data))
            return result
        if view in check.DECLARATION_VIEWS:
            todo = [m for m in mods if m not in self.declaration_cache]
            if todo:
                data = json.loads(self.run_lean("--run", HELPER, "both", *todo))
                self.declaration_cache.update(data)
            return {m: set(self.declaration_cache[m][view]) for m in mods}
        return {m: set(us) for m, us in json.loads(self.run_lean("--run", HELPER, view, *mods)).items()}

    def test_meta_import_cannot_justify_removing_a_regular_import(self):
        self.write("C", "public import Init\n@[expose] public section\n"
                         "namespace Fixture\ndef value : Nat := 7\nend Fixture\n")
        self.compile("C")
        self.write("A", "import VerifiedGarbage.C\nmeta import VerifiedGarbage.C\n"
                         "private def answer : Nat := Fixture.value\n")
        self.compile("A")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.A"],
                                 {str(check.graph_path("VerifiedGarbage.A")): (["import VerifiedGarbage.C"], [])},
                                 check.Graph([self.root]), uses=self.uses)
        self.assertNotIn(check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.C"), plan.edits)

    def test_keep_all_consumer_retains_its_boundary_while_independent_work_builds(self):
        self.write("C", "public import VerifiedGarbage.B\n")
        self.compile("C")
        self.write("D", "import VerifiedGarbage.C\nprivate theorem useWitness : True := Fixture.witness\n")
        path = self.root / "VerifiedGarbage/D.lean"
        path.write_text(path.read_text().replace("module\n", "module -- shake: keep-all\n", 1))
        self.compile("D")
        self.write("E", "import VerifiedGarbage.B\nprivate theorem okay : True := True.intro\n")
        self.compile("E")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.C", "VerifiedGarbage.E"], {
                str(check.graph_path("VerifiedGarbage.C")): (["public import VerifiedGarbage.B"], []),
                str(check.graph_path("VerifiedGarbage.E")): (["import VerifiedGarbage.B"], []),
            }, check.Graph([self.root]), uses=self.uses,
                library=["VerifiedGarbage.C", "VerifiedGarbage.D", "VerifiedGarbage.E"])
            self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.E", "remove", "VerifiedGarbage.B")])
            self.assertEqual(plan.deferred[0]["kept_importers"], ["VerifiedGarbage.D"])
            check.fix(plan)
        for name in ("C", "D", "E"):
            self.compile(name)

    def test_public_repair_can_preserve_a_pinned_private_import(self):
        self.write("C", "import VerifiedGarbage.B -- shake: keep\n")
        self.compile("C")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(check.Plan(edits=[check.Edit("VerifiedGarbage.C", "add_public", "VerifiedGarbage.B")]))
        self.compile("C")
        self.write("D", "public import VerifiedGarbage.C\n"
                         "@[expose] public def forwarded : True := Fixture.witness\n")
        self.compile("D")

    def meta_plan(self):
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root])
            shaken = replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses)
            return check.analyze(["VerifiedGarbage.A"], shaken, graph, uses=self.uses,
                                 library=["VerifiedGarbage.A"])

    def test_cross_target_repairs_are_deferred_without_blocking_independent_narrowing(self):
        markers = ["VerifiedGarbage.TCB.Arm.Marker", "VerifiedGarbage.TCB.X86_64.Marker"]
        owner, bridge = "VerifiedGarbage.Proof.X86_64.C", "VerifiedGarbage.Proof.Bridge"
        boundary, consumer = "VerifiedGarbage.Proof.Boundary", "VerifiedGarbage.Proof.Arm.A"
        independent = "VerifiedGarbage.Proof.Independent"
        modules = markers + [owner, bridge, boundary, consumer, independent]
        for mod in markers:
            self.write_module(mod, "")
            self.compile_module(mod)
        self.write_module(owner, "@[expose] public def value : Nat := 7\n")
        self.compile_module(owner)
        self.write_module(bridge, f"public import {owner}\n")
        self.compile_module(bridge)
        for downstream in (False, True):
            with self.subTest(downstream=downstream):
                self.write_module(boundary, f"public import {bridge}\n")
                self.compile_module(boundary)
                self.write_module(consumer, f"public import {boundary if downstream else bridge}\n"
                                  "@[expose] public def answer : Nat := value\n")
                self.compile_module(consumer)
                self.write_module(independent, f"public import {bridge}\n")
                self.compile_module(independent)
                selected = [boundary if downstream else consumer, independent]
                with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent), \
                        mock.patch.object(import_discipline, "LEAN", self.root / "VerifiedGarbage"), \
                        mock.patch.object(import_discipline, "ROOT", self.root.parent):
                    self.assertEqual(import_discipline.main(), 0)
                    graph = check.Graph([self.root])
                    shaken = replay.discover(selected, {}, graph, self.uses)
                    plan = check.analyze(selected, shaken, graph, uses=self.uses, library=modules)
                    self.assertEqual(plan.edits, [check.Edit(independent, "remove_public", bridge)])
                    witness = next(d for d in plan.deferred if "repository discipline" in d["reason"])
                    self.assertEqual(witness["module"], selected[0])
                    self.assertEqual(witness["invalid_repairs"][0]["module"], consumer)
                    self.assertEqual(witness["invalid_repairs"][0]["dependency"], owner)
                    check.fix(plan)
                    self.assertEqual(import_discipline.main(), 0)
                self.compile_module(consumer)
                self.compile_module(independent)

    def test_unused_private_meta_import_is_removed_and_rebuilds(self):
        self.write("A", "meta import VerifiedGarbage.B\nprivate def okay : Nat := 7\n")
        self.compile("A")
        plan = self.meta_plan()
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.A", "remove_meta", "VerifiedGarbage.B")])
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(plan)
        self.compile("A")

    def initializer_fixture(self, generated=False):
        self.write("E", "public initialize counter : IO.Ref Nat ← IO.mkRef 0\n")
        self.compile("E")
        if generated:
            self.write("D", "public meta import Lean\npublic import VerifiedGarbage.E\n"
                             'macro "bump_counter" : command => `(initialize counter.modify fun n => n + 1)\n')
            self.compile("D")
            self.write("C", "import VerifiedGarbage.D\nbump_counter\n")
        else:
            self.write("C", "import VerifiedGarbage.E\ninitialize counter.modify fun n => n + 1\n")
        self.compile("C")
        self.write("A", "import VerifiedGarbage.E\nimport VerifiedGarbage.C\n"
                         "meta import VerifiedGarbage.E\nmeta import VerifiedGarbage.C\n#eval counter.get\n")
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "1")

    def test_runtime_initializer_hidden_from_olean_and_terms_is_retained(self):
        self.initializer_fixture()
        self.assertIn("Lean.regularInitAttr", self.uses(["VerifiedGarbage.C"], "effects")["VerifiedGarbage.C"])
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "1")

    def test_macro_generated_runtime_initializer_is_detected_in_ir(self):
        self.initializer_fixture(generated=True)
        source = (self.root / "VerifiedGarbage/C.lean").read_text()
        self.assertNotIn("initialize", source)
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        decisions = [d for d in plan.decisions if d["dependency"] == "VerifiedGarbage.C"]
        self.assertTrue(decisions)
        for decision in decisions:
            self.assertEqual(decision["reason"], "opaque_module_effects")
            self.assertIn("Lean.regularInitAttr", decision["evidence"]["extensions"])
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "1")

    def test_initializer_order_uses_declaration_paths_as_well_as_meta_paths(self):
        self.write("E", "public initialize counter : IO.Ref Nat ← IO.mkRef 0\n")
        self.compile("E")
        for name, digit in (("C", 1), ("D", 2)):
            self.write(name, "import VerifiedGarbage.E\n"
                       f"initialize counter.modify fun n => n * 10 + {digit}\n")
            self.compile(name)
        self.write("B", "public import VerifiedGarbage.C\n")
        self.compile("B")
        for ordinary_anchors in (False, True):
            with self.subTest(ordinary_anchors=ordinary_anchors):
                anchors = "import VerifiedGarbage.C\nimport VerifiedGarbage.D\n" if ordinary_anchors else ""
                self.write("A", "import VerifiedGarbage.E\n" + anchors
                           + "meta import VerifiedGarbage.B\nmeta import VerifiedGarbage.D\n"
                             "meta import VerifiedGarbage.C\nmeta import VerifiedGarbage.E\n#eval counter.get\n")
                self.compile("A")
                self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "12")
                plan = self.meta_plan()
                removal = check.Edit("VerifiedGarbage.A", "remove_meta", "VerifiedGarbage.B")
                if ordinary_anchors:
                    self.assertIn(removal, plan.edits)
                else:
                    self.assertNotIn(removal, plan.edits)
                    self.assertTrue(any(d["reason"] == "would reorder opaque initialization" for d in plan.deferred))
                with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
                    check.fix(plan)
                self.compile("A")
                self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "12")

    def test_private_meta_import_used_only_during_evaluation_is_retained(self):
        self.write("B", "public def value : Nat := 7\n")
        self.compile("B")
        self.write("A", "meta import VerifiedGarbage.B\n#eval value\n")
        self.compile("A")
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        decision = next(d for d in plan.decisions if d["dependency"] == "VerifiedGarbage.B")
        self.assertEqual(decision["status"], "retained")

    def test_private_meta_provider_of_an_evaluated_transitive_definition_is_retained(self):
        self.write("C", "public def value : Nat := 7\n")
        self.compile("C")
        self.write("B", "public import VerifiedGarbage.C\n")
        self.compile("B")
        self.write("A", "meta import VerifiedGarbage.B\n#eval value\n")
        self.compile("A")
        self.assertFalse(self.meta_plan().edits)

    def test_private_removal_repairs_an_import_all_consumer(self):
        self.write("C", "import VerifiedGarbage.B\n")
        self.compile("C")
        self.write("D", "import all VerifiedGarbage.C\nprivate theorem useWitness : True := Fixture.witness\n")
        self.compile("D")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.C"],
                                 {str(check.graph_path("VerifiedGarbage.C")): (["import VerifiedGarbage.B"], [])},
                                 check.Graph([self.root]), uses=self.uses,
                                 library=["VerifiedGarbage.C", "VerifiedGarbage.D"])
            self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.C", "remove", "VerifiedGarbage.B"),
                                               check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.B")})
            check.fix(plan)
        self.compile("C")
        self.compile("D")

    def test_private_meta_removal_repairs_an_import_all_consumer(self):
        self.write("B", "public def value : Nat := 7\n")
        self.compile("B")
        self.write("C", "meta import VerifiedGarbage.B\n")
        self.compile("C")
        self.write("D", "import all VerifiedGarbage.C\n#eval value\n")
        self.compile("D")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.C"],
                                 {str(check.graph_path("VerifiedGarbage.C")): (["meta import VerifiedGarbage.B"], [])},
                                 check.Graph([self.root]), uses=self.uses,
                                 library=["VerifiedGarbage.C", "VerifiedGarbage.D"])
            self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.C", "remove_meta", "VerifiedGarbage.B"),
                                               check.Edit("VerifiedGarbage.D", "add_meta", "VerifiedGarbage.B")})
            check.fix(plan)
        self.compile("C")
        self.compile("D")

    def test_erased_evaluation_instance_is_retained_in_both_phases(self):
        self.write("C", "@[expose] public section\nclass Chosen where\n  value : Nat\n"
                         "def chosen [Chosen] : Nat := Chosen.value\n")
        self.compile("C")
        self.write("B", "public import VerifiedGarbage.C\npublic instance : Chosen := ⟨7⟩\n")
        self.compile("B")
        self.write("A", "import VerifiedGarbage.B\nmeta import VerifiedGarbage.B\n"
                         "meta import VerifiedGarbage.C\n#eval chosen\n")
        self.compile("A")
        # The instance is selected only in a temporary evaluated declaration.
        self.assertNotIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "references")["VerifiedGarbage.A"])
        self.assertFalse(self.uses(["VerifiedGarbage.A"], "meta_private")["VerifiedGarbage.A"])
        self.assertFalse(self.meta_plan().edits)

    def temporary_registry_case(self, attribute, tactic, extension):
        self.write("C", "@[expose] public def foo (n : Nat) : Nat := 0 + n\n")
        self.compile("C")
        self.write("B", "public import VerifiedGarbage.C\n"
                         f"@[{attribute}] public theorem foo_eq (n : Nat) : foo n = n := by simp [foo]\n")
        self.compile("B")
        self.write("A", f"import VerifiedGarbage.B\n#check fun n : Nat => (show foo n = n by {tactic})\n")
        self.compile("A")
        self.assertNotIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "references")["VerifiedGarbage.A"])
        self.assertNotIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "private")["VerifiedGarbage.A"])
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        decision = next(d for d in plan.decisions if d["dependency"] == "VerifiedGarbage.B")
        self.assertEqual(decision["reason"], "opaque_module_effects")
        self.assertEqual(decision["evidence"]["extensions"], [extension])

    def test_simp_registry_used_only_by_a_temporary_check_is_retained(self):
        self.temporary_registry_case("simp", "simp", "Lean.Meta.simpExtension")

    def test_grind_registry_used_only_by_a_temporary_check_is_retained(self):
        self.temporary_registry_case("grind =", "grind", "Lean.Meta.Grind.grindExt")

    def test_arbitrarily_named_aesop_registry_is_retained(self):
        packages = REPO_LEAN / ".lake/packages"
        if not (packages / "aesop/.lake/build/lib/lean/Aesop.olean").is_file():
            self.skipTest("Aesop package cache is not installed")
        self.env["LEAN_PATH"] = os.pathsep.join([str(self.root)] + [
            str(p / ".lake/build/lib/lean") for p in packages.iterdir() if p.is_dir()])
        self.write("C", "@[expose] public def foo (n : Nat) : Nat := 0 + n\n")
        self.compile("C")
        self.write("B", "import Aesop\npublic import VerifiedGarbage.C\n"
                         "@[aesop safe apply] public theorem foo_eq (n : Nat) : foo n = n := by simp [foo]\n")
        self.compile("B")
        self.write("A", "import Aesop\nimport VerifiedGarbage.B\n"
                         "#check fun n : Nat => (show foo n = n by aesop)\n")
        self.compile("A")
        self.assertNotIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "references")["VerifiedGarbage.A"])
        self.assertNotIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "private")["VerifiedGarbage.A"])
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        self.assertEqual(plan.decisions[0]["evidence"]["extensions"], ["default"])

    def test_generated_instances_are_detected_in_exported_extension_metadata(self):
        self.write("C", "@[expose] public section\nclass Chosen where\n  value : Nat\n"
                         "def chosen [Chosen] : Nat := Chosen.value\n")
        self.compile("C")
        self.write("D", 'import Lean\npublic import VerifiedGarbage.C\n'
                         'macro "install_chosen" : command => `(public instance : Chosen := ⟨7⟩)\n')
        self.compile("D")
        self.write("B", "public import VerifiedGarbage.C\nimport VerifiedGarbage.D\ninstall_chosen\n")
        self.compile("B")
        self.write("A", "import VerifiedGarbage.B\nmeta import VerifiedGarbage.B\n"
                         "meta import VerifiedGarbage.C\n#eval chosen\n")
        self.compile("A")
        effects = self.uses(["VerifiedGarbage.B"], "effects")["VerifiedGarbage.B"]
        self.assertIn(check.INSTANCE_EXTENSION, effects)
        with mock.patch.object(check, "LEAN", self.root):
            graph = check.Graph([self.root])
            self.assertFalse(graph.kept("VerifiedGarbage.B"))
            check.prepare_effects(graph, ["VerifiedGarbage.B"], self.uses)
            self.assertTrue(graph.kept("VerifiedGarbage.B"))
        self.assertFalse(self.meta_plan().edits)

    def test_empty_exported_namespace_is_a_real_import_dependency(self):
        for extra in ("", "namespace Other\npublic def value : Nat := 7\nend Other\n"):
            self.write("B", "public section\nnamespace UnrecordedNamespace73129\n"
                             "end UnrecordedNamespace73129\n" + extra)
            self.compile("B")
            self.write("A", "import VerifiedGarbage.B\nopen UnrecordedNamespace73129\n"
                             "private theorem okay : True := True.intro\n")
            self.compile("A")
            self.assertNotIn("UnrecordedNamespace73129",
                             self.uses(["VerifiedGarbage.B"], "namespaces")["VerifiedGarbage.B"])
            self.assertIn("UnrecordedNamespace73129",
                          self.uses(["VerifiedGarbage.B"], "namespace_exports")["VerifiedGarbage.B"])
            self.assertFalse(self.meta_plan().edits)

    def test_an_alternative_empty_namespace_provider_allows_narrowing(self):
        for name in ("B", "C"):
            self.write(name, "public section\nnamespace UnrecordedNamespace73129\nend UnrecordedNamespace73129\n")
            self.compile(name)
        self.write("A", "import VerifiedGarbage.B\nimport VerifiedGarbage.C\n"
                         "open UnrecordedNamespace73129\nprivate theorem okay : True := True.intro\n")
        self.compile("A")
        plan = self.meta_plan()
        self.assertEqual(plan.edits, [check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B")])
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(plan)
        self.compile("A")

    def test_public_narrowing_repairs_an_empty_namespace_consumer(self):
        self.write("B", "public section\nnamespace UnrecordedNamespace73129\nend UnrecordedNamespace73129\n")
        self.compile("B")
        self.write("A", "public import VerifiedGarbage.B\n")
        self.compile("A")
        self.write("D", "import VerifiedGarbage.A\nopen UnrecordedNamespace73129\n")
        self.compile("D")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.A"],
                                 {str(check.graph_path("VerifiedGarbage.A")): (["public import VerifiedGarbage.B"], [])},
                                 check.Graph([self.root]), uses=self.uses,
                                 library=["VerifiedGarbage.A", "VerifiedGarbage.D"])
            self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.A", "remove_public", "VerifiedGarbage.B"),
                                               check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.B")})
            check.fix(plan)
        self.compile("A")
        self.compile("D")

    def test_downstream_repair_after_a_multiline_import_comment_compiles(self):
        self.write("C", "@[expose] public def commentFixtureValue : Nat := 7\n")
        self.compile("C")
        for tail in (" explanation -/\n", " explanation -/ /-! documentation -/\n", " explanation -/ "):
            self.write("P", "public import VerifiedGarbage.C\n")
            self.compile("P")
            self.write("A", "import VerifiedGarbage.B\nimport VerifiedGarbage.P /- why\n" + tail
                             + "private def answer : Nat := commentFixtureValue\n"
                             + "private theorem witness : True := Fixture.witness\n")
            self.compile("A")
            with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
                plan = check.analyze(["VerifiedGarbage.P"],
                                     {str(check.graph_path("VerifiedGarbage.P")): (["public import VerifiedGarbage.C"], [])},
                                     check.Graph([self.root]), uses=self.uses,
                                     library=["VerifiedGarbage.P", "VerifiedGarbage.A"])
                self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.P", "remove_public", "VerifiedGarbage.C"),
                                                   check.Edit("VerifiedGarbage.A", "add", "VerifiedGarbage.C")})
                check.fix(plan)
            self.compile("P")
            self.compile("A")

    def test_first_added_import_follows_prelude_and_its_comment(self):
        self.write("A", "prelude /- explanation\n continued -/\n")
        self.compile("A")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(check.Plan(edits=[check.Edit("VerifiedGarbage.A", "add", "VerifiedGarbage.B")]))
        self.compile("A")

    def instance_order_fixture(self, imports, public=True):
        self.write("E", "@[expose] public section\nclass Chosen where\n  value : Nat\n"
                         "def chosen [Chosen] : Nat := Chosen.value\n")
        self.compile("E")
        for name, value in (("C", 1), ("D", 2)):
            self.write(name, f"public import VerifiedGarbage.E\npublic instance choice{name} : Chosen := ⟨{value}⟩\n")
            self.compile(name)
        self.write("B", "public import VerifiedGarbage.C\n")
        self.compile("B")
        visibility = "@[expose] public" if public else "private"
        self.write("A", imports + f"{visibility} def chosenValue : Nat := chosen\n#eval chosenValue\n")
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "2")

    def assert_chosen_value_unchanged(self):
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "2")

    def test_public_narrowing_keeps_a_private_initialization_anchor(self):
        self.instance_order_fixture("public import VerifiedGarbage.B\npublic import VerifiedGarbage.D\n"
                                    "meta import VerifiedGarbage.B\nmeta import VerifiedGarbage.D\n")
        plan = self.meta_plan()
        self.assertIn(check.Edit("VerifiedGarbage.A", "demote", "VerifiedGarbage.B"), plan.edits)
        self.assertNotIn(check.Edit("VerifiedGarbage.A", "remove_public", "VerifiedGarbage.B"), plan.edits)
        self.assertTrue(any(d.get("private_anchor_retained") for d in plan.deferred))
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(plan)
        self.assert_chosen_value_unchanged()
        # A later round must not undo the order protection by deleting B.
        self.assertFalse(self.meta_plan().edits)

    def test_private_removal_cannot_reorder_surviving_instances(self):
        self.instance_order_fixture("import VerifiedGarbage.B\npublic import VerifiedGarbage.D\n"
                                    "public import VerifiedGarbage.C\nmeta import VerifiedGarbage.B\n"
                                    "meta import VerifiedGarbage.D\nmeta import VerifiedGarbage.C\n")
        plan = self.meta_plan()
        self.assertFalse(plan.edits)
        self.assertTrue(any(d["reason"] == "would reorder opaque initialization" for d in plan.deferred))
        self.assert_chosen_value_unchanged()

    def test_demotion_preserves_an_earlier_public_copy_before_a_private_duplicate(self):
        self.instance_order_fixture("public import VerifiedGarbage.B\npublic import VerifiedGarbage.D\n"
                                    "import VerifiedGarbage.B\nmeta import VerifiedGarbage.B\n"
                                    "meta import VerifiedGarbage.D\n", public=False)
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(check.Plan(edits=[check.Edit("VerifiedGarbage.A", "demote", "VerifiedGarbage.B")]))
        self.assert_chosen_value_unchanged()

    def test_moving_past_structural_data_does_not_need_an_initialization_anchor(self):
        self.write("E", "@[expose] public section\nclass Chosen where\n  value : Nat\n"
                         "def chosen [Chosen] : Nat := Chosen.value\n")
        self.compile("E")
        self.write("C", "public import VerifiedGarbage.E\npublic instance choiceC : Chosen := ⟨1⟩\n")
        self.compile("C")
        self.write("D", "public import VerifiedGarbage.E\n@[expose] public def unrelated : Nat := 0\n")
        self.compile("D")
        self.write("B", "public import VerifiedGarbage.C\n")
        self.compile("B")
        self.write("A", "public import VerifiedGarbage.B\npublic import VerifiedGarbage.D\n"
                         "meta import VerifiedGarbage.B\nmeta import VerifiedGarbage.D\n"
                         "@[expose] public def chosenValue : Nat := chosen + unrelated\n#eval chosenValue\n")
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "1")
        plan = self.meta_plan()
        self.assertIn(check.Edit("VerifiedGarbage.A", "remove_public", "VerifiedGarbage.B"), plan.edits)
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            check.fix(plan)
        self.compile("A")
        self.assertEqual(self.run_lean(self.root / "VerifiedGarbage/A.lean").strip(), "1")

    def phase_repair(self, body, expected):
        self.write("C", "public import Init\n@[expose] public section\n"
                         "namespace Fixture\ndef value : Nat := 7\nend Fixture\n")
        self.compile("C")
        self.write("B", "public import Init\npublic meta import VerifiedGarbage.C\n"
                         "public meta section\nnamespace Fixture\ndef wrapper : Nat := value\nend Fixture\n")
        self.compile("B")
        self.write("A", "public import VerifiedGarbage.B\n@[expose] public section\n"
                         "theorem okay : True := True.intro\n")
        self.compile("A")
        self.write("D", "public import VerifiedGarbage.A\n" + body)
        self.compile("D")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            plan = check.analyze(["VerifiedGarbage.A"],
                                 {str(check.graph_path("VerifiedGarbage.A")): (["public import VerifiedGarbage.B"], [])},
                                 check.Graph([self.root]), uses=self.uses,
                                 library=["VerifiedGarbage.A", "VerifiedGarbage.D"])
            self.assertIn(expected, plan.edits, {m: {v: sorted(self.uses([m], v)[m]) for v in check.DECLARATION_VIEWS}
                                                for m in ("VerifiedGarbage.A", "VerifiedGarbage.D")})
            check.fix(plan)
        self.compile("A")
        self.compile("D")

    def test_public_meta_body_receives_a_public_meta_repair(self):
        self.phase_repair("public meta section\ndef answer : Nat := Fixture.value\n",
                          check.Edit("VerifiedGarbage.D", "add_public_meta", "VerifiedGarbage.C"))

    def test_meta_declaration_is_repaired_with_an_ordinary_import(self):
        self.phase_repair("public meta section\ndef answer : Nat := Fixture.wrapper\n",
                          check.Edit("VerifiedGarbage.D", "add_public", "VerifiedGarbage.B"))

    def test_evaluation_receives_a_private_meta_repair(self):
        self.phase_repair("#eval Fixture.value\n",
                          check.Edit("VerifiedGarbage.D", "add_meta", "VerifiedGarbage.C"))

    def test_evaluating_a_meta_definition_receives_an_ordinary_repair(self):
        self.phase_repair("#guard Fixture.wrapper == 7\n",
                          check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.B"))

    def test_resolved_references_remove_a_suffix_collision(self):
        self.write("C", "public import Init\n@[expose] public section\n"
                         "namespace Fixture.CName\ntheorem derive : True := True.intro\nend Fixture.CName\n")
        self.compile("C")
        self.write("A", "import VerifiedGarbage.B\npublic import VerifiedGarbage.C\n"
                         "@[expose] public section\nnamespace Fixture.A\nopen Fixture\n"
                         "theorem result : True := CName.derive\nend Fixture.A\n")
        self.compile("A")
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root])
            plan = check.analyze(["VerifiedGarbage.A"],
                                 {str(check.graph_path("VerifiedGarbage.A")): (["import VerifiedGarbage.B"], [])},
                                 graph, uses=self.uses)
            self.assertIn(check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B"), plan.edits)
            check.fix(plan)
        self.compile("A")

    def test_implicit_init_preserves_both_phases_when_an_import_is_removed(self):
        self.write("A", "import VerifiedGarbage.B\npublic def answer : Nat := 7\n#guard answer == 7\n")
        self.compile("A")
        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root, prefix / "src/lean"])
            suggestions = replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses)
            plan = check.analyze(["VerifiedGarbage.A"], suggestions, graph, uses=self.uses)
            self.assertIn(check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B"), plan.edits)
            check.fix(plan)
        self.compile("A")

    def test_demotion_does_not_add_redundant_repairs_of_implicit_core_imports(self):
        self.write("A", "public import VerifiedGarbage.B\npublic meta def answer : Nat := 7\n")
        self.compile("A")
        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root, prefix / "src/lean"])
            suggestions = replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses)
            plan = check.analyze(["VerifiedGarbage.A"], suggestions, graph, uses=self.uses)
            self.assertIn(check.Edit("VerifiedGarbage.A", "remove_public", "VerifiedGarbage.B"), plan.edits)
            self.assertFalse([e for e in plan.edits if e.dependency.startswith("Init")], plan.edits)
            check.fix(plan)
        self.compile("A")

    def test_unused_public_provider_is_removed_with_its_repairs_in_one_plan(self):
        self.write("C", "public import Init\n@[expose] public section\n"
                         "namespace Fixture\ndef value : Nat := 7\nend Fixture\n")
        self.compile("C")
        self.write("B", "public import VerifiedGarbage.C\n")
        self.compile("B")
        self.write("A", "public import VerifiedGarbage.B\n@[expose] public def answer : Nat := Fixture.value\n")
        self.compile("A")
        self.write("D", "public import VerifiedGarbage.A\n@[expose] public def downstream : Nat := answer\n")
        self.compile("D")

        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root, prefix / "src/lean"])
            suggestions = replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses)
            plan = check.analyze(["VerifiedGarbage.A"], suggestions, graph, uses=self.uses,
                                 library=["VerifiedGarbage.A", "VerifiedGarbage.D"])
            self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.A", "remove_public", "VerifiedGarbage.B"),
                                               check.Edit("VerifiedGarbage.A", "add_public", "VerifiedGarbage.C")})
            check.fix(plan)
        self.compile("A")
        self.compile("D")

    def test_duplicate_private_then_public_import_can_be_narrowed(self):
        self.write("A", "import VerifiedGarbage.B\npublic import VerifiedGarbage.B\n"
                         "public theorem result : True := Fixture.witness\n")
        self.compile("A")
        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root, prefix / "src/lean"])
            plan = check.analyze(["VerifiedGarbage.A"], replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses),
                                 graph, uses=self.uses)
            self.assertIn(check.Edit("VerifiedGarbage.A", "demote", "VerifiedGarbage.B"), plan.edits)
            check.fix(plan)
        self.compile("A")

    def test_exposed_proof_field_counts_as_public(self):
        self.write("A", "public import VerifiedGarbage.B\n\n@[expose] public section\n"
                         "namespace Fixture\ndef packaged : { p : Prop // p } := ⟨True, witness⟩\nend Fixture\n")
        self.compile("A")
        self.assertIn("VerifiedGarbage.B", self.uses(["VerifiedGarbage.A"], "public")["VerifiedGarbage.A"])

    def test_exposed_auxiliary_upgrades_from_type_to_body(self):
        # Minimized from Proof.Dsa.X86.RandomSignInstance. A0's exported
        # _proof_N statements precede signFn in the reader's worklist. Reading
        # their types must not suppress a later traversal of their bodies.
        self.write_module("Fixture.Types", "public import Init\n@[expose] public section\n"
                          "namespace Fixture\nabbrev NoSp (n : Nat) : Prop := ∀ i, i ≤ n → True\n"
                          "structure SignFn where\n n : Nat\n noSp : NoSp n\n depth : n ≤ 1\nend Fixture\n")
        self.compile_module("Fixture.Types")
        self.write_module("Fixture.Support", "public import Fixture.Types\n@[expose] public section\n"
                          "namespace Fixture\ntheorem NoSp.of_all {n : Nat} (_ : n = 0) : NoSp n :=\n"
                          " fun _ _ => True.intro\nend Fixture\n")
        self.compile_module("Fixture.Support")
        self.write_module("Fixture.A0", "public import Fixture.Support\n@[expose] public section\n"
                          "namespace Fixture.A0\ndef signFn : Fixture.SignFn where\n n := 0\n"
                          " noSp := Fixture.NoSp.of_all (by decide +kernel)\n"
                          " depth := by decide +kernel\nend Fixture.A0\n")
        self.compile_module("Fixture.A0")
        self.assertIn("Fixture.Support", self.uses(["Fixture.A0"], "public")["Fixture.A0"])

    def test_combined_demotion_repairs_compile_with_public_visibility(self):
        for name in ("A", "C"):
            self.write(name, "public import VerifiedGarbage.B\n\n@[expose] public section\n"
                             f"namespace Fixture\ntheorem {name.lower()} : True := witness\nend Fixture\n")
            self.compile(name)
        self.write("D", "public import VerifiedGarbage.A\npublic import VerifiedGarbage.C\n\n"
                         "@[expose] public section\nnamespace Fixture\n"
                         "def packaged : { p : Prop // p } := ⟨True, witness⟩\nend Fixture\n")
        self.compile("D")
        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            mods = ["VerifiedGarbage.A", "VerifiedGarbage.C"]
            graph = check.Graph([self.root, prefix / "src/lean"])
            shaken = {str(check.graph_path(m)): (["public import VerifiedGarbage.B"], []) for m in mods}
            plan = check.analyze(mods, shaken, graph, uses=self.uses,
                                 library=mods + ["VerifiedGarbage.B", "VerifiedGarbage.D"])
            self.assertIn(check.Edit("VerifiedGarbage.D", "add_public", "VerifiedGarbage.B"), plan.edits)
            check.fix(plan)
        for name in ("A", "C", "D"):
            self.compile(name)


    def test_one_component_module_owner_survives_reader_serialization(self):
        self.write_module("RootProvider", "public import Init\n@[expose] public section\n"
                          "namespace SingleRoot\ndef value : Nat := 7\nend SingleRoot\n")
        self.compile_module("RootProvider")
        self.write_module("Fixture.Consumer", "public import RootProvider\n"
                          "@[expose] public def answer : Nat := SingleRoot.value\n")
        self.compile_module("Fixture.Consumer")
        self.assertIn("RootProvider", self.uses(["Fixture.Consumer"], "public")["Fixture.Consumer"])

    def private_provider(self, meta=False, effect=False):
        self.write("B", "public import Init\n@[expose] public section\nnamespace Fixture\n"
                         "def value : Nat := 7\ndef unused : Nat := 9\n"
                         "theorem witness : True := True.intro\ntheorem unusedFact : (0 : Nat) = 0 := rfl\nend Fixture\n")
        self.compile("B")
        if effect:
            self.write("E", "public import VerifiedGarbage.B\nattribute [simp] Fixture.unusedFact\n")
            self.compile("E")
        self.write("C", ("public meta import " if meta else "public import ") + "VerifiedGarbage.B\n"
                         + ("public import VerifiedGarbage.E\n" if effect else ""))
        self.compile("C")
        self.write("A", "import VerifiedGarbage.C\n" + ("#guard Fixture.value == 7\n" if meta else
                         "public theorem result : True := Fixture.witness\n"))
        self.compile("A")
        prefix = pathlib.Path(self.run_lean("--print-prefix").strip())
        with mock.patch.object(check, "LEAN", self.root), mock.patch.object(check, "ROOT", self.root.parent):
            graph = check.Graph([self.root, prefix / "src/lean"])
            plan = check.analyze(["VerifiedGarbage.A"], replay.discover(["VerifiedGarbage.A"], {}, graph, self.uses),
                                 graph, uses=self.uses)
            if effect:
                self.assertNotIn(check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.C"), plan.edits)
                self.assertFalse(plan.edits)
            else:
                self.assertEqual(set(plan.edits), {check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.C"),
                                                   check.Edit("VerifiedGarbage.A", "add_meta" if meta else "add", "VerifiedGarbage.B")})
                check.fix(plan)
        self.compile("A")

    def test_private_provider_can_be_replaced_by_its_used_owner(self):
        self.private_provider()

    def test_private_meta_provider_is_replaced_in_the_original_phase(self):
        self.private_provider(meta=True)

    def test_private_provider_replacement_preserves_unknown_effects(self):
        self.private_provider(effect=True)


if __name__ == "__main__":
    unittest.main()
