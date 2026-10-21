"""Visibility contracts checked against small compiled Lean phase fixtures."""

import unittest
import random

import check_lean_public_imports as check

from lean_import_graph import VisibilityGraph


class Graph(VisibilityGraph):
    def __init__(self, edges):
        super().__init__()
        self.edges = edges

    def imports(self, mod):
        return self.edges.get(mod, [])


class Visibility(unittest.TestCase):
    def test_meta_import_is_not_an_ordinary_provider(self):
        graph = Graph({"A": [("B", False, True, False)], "B": [("C", True, False, False)]})
        self.assertEqual(graph.reads("A"), set())
        self.assertEqual(graph.reads("A", True), {"B", "C"})

    def test_ordinary_import_carries_public_meta_exports(self):
        graph = Graph({"A": [("B", True, False, False)], "B": [("C", True, True, False)]})
        self.assertEqual(graph.passes("A"), {"A", "B"})
        self.assertEqual(graph.meta_exports("A"), {"C"})
        self.assertEqual(graph.reads("A", True), {"C"})

    def test_private_import_keeps_meta_access_local(self):
        graph = Graph({"D": [("A", False, False, False)], "A": [("B", False, False, False)],
                       "B": [("C", True, True, False)]})
        self.assertEqual(graph.reads("A", True), {"C"})
        self.assertEqual(graph.meta_exports("A"), set())
        self.assertEqual(graph.reads("D", True), set())

    def test_public_meta_edge_also_exposes_public_ordinary_descendants_as_meta(self):
        graph = Graph({"A": [("B", True, True, False)], "B": [("C", True, False, False)]})
        self.assertEqual(graph.passes("A"), {"A"})
        self.assertEqual(graph.meta_exports("A"), {"B", "C"})

    def test_import_all_reads_private_ordinary_dependencies(self):
        graph = Graph({"A": [("B", False, False, True)], "B": [("C", False, False, False)]})
        self.assertEqual(graph.reads("A"), {"B", "C"})
        self.assertEqual(graph.passes("A"), {"A"})

    def test_meta_import_all_does_not_leak_ordinary_access(self):
        graph = Graph({"A": [("B", False, True, True)], "B": [("C", False, False, False)]})
        self.assertEqual(graph.reads("A"), set())
        self.assertEqual(graph.reads("A", True), {"B"})

    def test_meta_cycle_fails_instead_of_hanging(self):
        graph = Graph({"A": [("B", True, True, False)], "B": [("A", True, False, False)]})
        with self.assertRaisesRegex(ValueError, "cyclic"):
            graph.meta_exports("A")

    def test_reused_closures_match_fresh_graphs_after_mixed_edits(self):
        class Source(check.Graph):
            def __init__(self, edges):
                super().__init__([])
                self.edges = edges

            def imports(self, mod):
                return self.edges.get(mod, [])

        rng = random.Random(76)
        for trial in range(30):
            modules = [f"M{i}" for i in range(24)]
            edges = {m: [] for m in modules}
            for i, mod in enumerate(modules):
                for dep in modules[i + 1:]:
                    if rng.random() < 0.12:
                        public, meta = rng.choice([False, True]), rng.choice([False, True])
                        edges[mod].append((dep, public, meta, not public and rng.random() < 0.15))
            original = Source(edges)
            for mod in reversed(modules):
                original.passes(mod)
                original.meta_exports(mod)
                original.reads(mod)
                original.reads(mod, True)
            edits = []
            for i, mod in enumerate(modules[:-1]):
                for dep, public, meta, all_ in edges[mod]:
                    if not (meta and public) and not all_ and rng.random() < 0.2:
                        action = rng.choice(["demote", "remove_public"]) if public else "remove_meta" if meta else "remove"
                        edits.append(check.Edit(mod, action, dep))
                dep = rng.choice(modules[i + 1:])
                edits.append(check.Edit(mod, rng.choice(["add", "add_public", "add_meta", "add_public_meta"]), dep))
            planned = check.Planned(original, edits)
            fresh = Graph({mod: planned.imports(mod) for mod in modules})
            for mod in modules:
                with self.subTest(trial=trial, mod=mod):
                    self.assertEqual(planned.passes(mod), fresh.passes(mod))
                    self.assertEqual(planned.meta_exports(mod), fresh.meta_exports(mod))
                    self.assertEqual(planned.reads(mod), fresh.reads(mod))
                    self.assertEqual(planned.reads(mod, True), fresh.reads(mod, True))

    def test_reuse_does_not_hide_a_cycle_introduced_by_a_public_repair(self):
        original = check.Graph([])
        original.imports = lambda mod: [("B", True, False, False)] if mod == "A" else []
        original.passes("A")
        planned = check.Planned(original, [check.Edit("B", "add_public", "A")])
        with self.assertRaisesRegex(ValueError, "cyclic"):
            planned.passes("A")

    def test_repairs_obey_target_and_trusted_layer_import_discipline(self):
        library = ["VerifiedGarbage.TCB.Arm.Marker", "VerifiedGarbage.TCB.X86_64.Marker"]
        cases = [
            ("VerifiedGarbage.Proof.Arm.A", "VerifiedGarbage.Proof.X86_64.C", False),
            ("VerifiedGarbage.TCB.Common.A", "Mathlib.Data.Nat.Basic", False),
            ("VerifiedGarbage.Spec.A", "VerifiedGarbage.Proof.C", False),
            ("VerifiedGarbage.Impl.A", "VerifiedGarbage.Proof.C", False),
            ("VerifiedGarbage.Proof.Arm.A", "VerifiedGarbage.Proof.Arm.C", True),
            ("VerifiedGarbage.Spec.A", "Mathlib.Data.Nat.Basic", True),
            ("VerifiedGarbage.Impl.A", "Lean.Elab.Command", True),
            ("VerifiedGarbage.TCB.Common.A", "Lean.Elab.Command", True),
        ]
        for module, owner, allowed in cases:
            for action in ("add", "add_public", "add_meta", "add_public_meta"):
                with self.subTest(module=module, owner=owner, action=action):
                    graph = check.Graph([])
                    graph.imports = lambda mod: [(owner, True, False, False)] if mod == "Bridge" else []
                    graph.importers = lambda mod, modules: set()
                    plan = check.Plan(edits=[check.Edit(module, "remove_public", "Bridge"),
                                             check.Edit(module, action, owner)])
                    guards = check.import_discipline_guards(plan, graph, library)
                    self.assertEqual(bool(guards), not allowed)
                    if not allowed:
                        self.assertEqual(guards[module, "Bridge"][0]["dependency"], owner)


if __name__ == "__main__":
    unittest.main()
