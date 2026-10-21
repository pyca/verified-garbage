"""Regression replay must run without Lean, builds or the original checkout."""

import copy
import json
import pathlib
import tempfile
import unittest
from unittest import mock

import check_lean_public_imports as check
import lean_import_replay as replay
import trim_lean_imports as trim

FIXTURE = pathlib.Path(__file__).parent / "fixtures/import_narrowing/diamond.json"


class Replay(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(FIXTURE.read_text())

    def test_portable_replay_has_no_process_or_source_access(self):
        with mock.patch.object(check, "LEAN", pathlib.Path("/different/checkout/lean")), \
                mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")), \
                mock.patch.object(check.subprocess, "Popen", side_effect=AssertionError("no processes")), \
                mock.patch.object(pathlib.Path, "read_text", side_effect=AssertionError("no source reads")):
            result = replay.replay(self.data)
        self.assertFalse(result["build_verified"])
        self.assertEqual(result["edits"], [
            {"module": "VerifiedGarbage.A", "action": "demote", "dependency": "VerifiedGarbage.B"},
            {"module": "VerifiedGarbage.C", "action": "demote", "dependency": "VerifiedGarbage.B"},
            {"module": "VerifiedGarbage.D", "action": "add_public", "dependency": "VerifiedGarbage.B"},
        ])
        self.assertEqual(result["cost"]["affected_modules"], 3)
        # Shared downstream work appears once, not once per candidate.
        self.assertEqual(result["cost"]["known_profile_work_seconds"], 7)

    def test_required_repairs_do_not_count_as_a_reduction_in_local_read_exposure(self):
        result = replay.replay(self.data)
        impact = result["visibility_impact"]
        self.assertTrue(impact["evaluated"])
        # A and C stop re-exporting B, but each still reads B privately. D
        # genuinely needs B and receives its own public import, so none of the
        # three consumers loses local access. Narrower boundaries alone aren't
        # evidence of fewer recompilations for this batch.
        self.assertEqual(impact["totals"]["ordinary_reads"], {"removed_pairs": 0, "added_pairs": 0})
        self.assertEqual(impact["totals"]["ordinary_reexports"], {"removed_pairs": 2, "added_pairs": 0})

    def test_captured_value_changing_removal_replays_with_a_private_order_anchor(self):
        data = json.loads(FIXTURE.with_name("instance_order.json").read_text())
        # The compiled regression evaluates to 2 before and after the fixed
        # plan. The former, successfully compiling removal evaluated to 1.
        # Retain that failure's real reader answers for fast planner iteration.
        with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")), \
                mock.patch.object(check.subprocess, "Popen", side_effect=AssertionError("no processes")), \
                mock.patch.object(pathlib.Path, "read_text", side_effect=AssertionError("no source reads")):
            result = replay.replay(data)
        self.assertFalse(result["build_verified"])
        self.assertIn({"module": "VerifiedGarbage.A", "action": "demote",
                       "dependency": "VerifiedGarbage.B"}, result["edits"])
        self.assertFalse(any(e["action"] == "remove_public" for e in result["edits"]))
        witness = next(d for d in result["deferred"] if d.get("private_anchor_retained"))
        self.assertEqual(witness["consumer"], "VerifiedGarbage.A")
        self.assertEqual(witness["original_order"], ["VerifiedGarbage.C", "VerifiedGarbage.D"])
        self.assertEqual(witness["proposed_order"], ["VerifiedGarbage.D", "VerifiedGarbage.C"])

    def test_captured_macro_initializer_is_protected_by_ir_evidence_without_lean(self):
        data = json.loads(FIXTURE.with_name("initializer.json").read_text())
        self.assertNotIn("initialize", data["sources"]["VerifiedGarbage.C"]["text"])
        with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")), \
                mock.patch.object(check.subprocess, "Popen", side_effect=AssertionError("no processes")), \
                mock.patch.object(pathlib.Path, "read_text", side_effect=AssertionError("no source reads")):
            result = replay.replay(data)
        self.assertFalse(result["build_verified"])
        self.assertFalse(result["edits"])
        decisions = [d for d in result["decisions"] if d["dependency"] == "VerifiedGarbage.C"]
        self.assertEqual({d["action"] for d in decisions}, {"remove", "remove_meta"})
        for decision in decisions:
            self.assertEqual(decision["reason"], "opaque_module_effects")
            self.assertIn("Lean.regularInitAttr", decision["evidence"]["extensions"])

    def test_target_discipline_replays_from_library_identities_without_directory_access(self):
        consumer, bridge = "VerifiedGarbage.Proof.Arm.A", "VerifiedGarbage.Proof.Bridge"
        owner, independent = "VerifiedGarbage.Proof.X86_64.C", "VerifiedGarbage.Proof.Independent"
        sources = {consumer: f"module\npublic import {bridge}\n",
                   bridge: f"module\npublic import {owner}\n",
                   owner: "module\n@[expose] public def value : Nat := 7\n",
                   independent: f"module\npublic import {bridge}\n"}
        uses = {v: {m: [] for m in sources} for v in
                (*check.DECLARATION_VIEWS, "effects", "references", "namespaces")}
        for view in ("public", "private", "references"):
            uses[view][consumer] = [owner]
        data = {"schema": 1, "independent": True, "selected": [consumer, independent],
                "library": [*sources, "VerifiedGarbage.TCB.Arm.Marker", "VerifiedGarbage.TCB.X86_64.Marker"],
                "modules": {"Init": False, **{m: True for m in sources}},
                "sources": {"Init": {"project": False, "text": "module\nprelude\n"},
                            **{m: {"project": True, "text": text} for m, text in sources.items()}},
                "users": {bridge: [consumer, independent], owner: [bridge]},
                "uses": uses, "shake": {consumer: [[], []], independent: [[], []]}, "profile": {}}
        with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")), \
                mock.patch.object(check.subprocess, "Popen", side_effect=AssertionError("no processes")), \
                mock.patch.object(pathlib.Path, "read_text", side_effect=AssertionError("no source reads")), \
                mock.patch.object(pathlib.Path, "iterdir", side_effect=AssertionError("no directory access")):
            result = replay.replay(data)
        self.assertEqual(result["edits"], [{"module": independent, "action": "remove_public", "dependency": bridge}])
        witness = next(d for d in result["deferred"] if "repository discipline" in d["reason"])
        self.assertEqual(witness["invalid_repairs"][0]["dependency"], owner)

    def test_an_unused_downstream_dependency_reduces_read_exposure(self):
        self.data["sources"]["VerifiedGarbage.D"]["text"] = (
            "module\npublic import VerifiedGarbage.A\npublic import VerifiedGarbage.C\n")
        for view in ("public", "private", "references"):
            self.data["uses"][view]["VerifiedGarbage.D"] = []
        result = replay.replay(self.data)
        self.assertFalse([e for e in result["edits"] if e["module"] == "VerifiedGarbage.D"])
        self.assertEqual(result["visibility_impact"]["totals"]["ordinary_reads"],
                         {"removed_pairs": 1, "added_pairs": 0})

    def test_private_removal_requires_potential_import_all_consumer_sources(self):
        self.data["selected"] = ["VerifiedGarbage.A"]
        self.data["sources"]["VerifiedGarbage.A"]["text"] = "module\nimport VerifiedGarbage.B\n"
        self.data["sources"]["VerifiedGarbage.B"]["text"] = "module\n"
        del self.data["sources"]["VerifiedGarbage.D"]
        self.data["shake"] = {"VerifiedGarbage.A": [["import VerifiedGarbage.B"], []]}
        for view in self.data["uses"]:
            self.data["uses"][view]["VerifiedGarbage.A"] = []
        # D could import all A, so its source is now core planning evidence.
        with self.assertRaisesRegex(replay.MissingEvidence, "source of VerifiedGarbage.D"):
            replay.replay(self.data)

    def test_missing_use_evidence_is_not_an_empty_set(self):
        del self.data["uses"]["public"]["VerifiedGarbage.D"]
        with self.assertRaisesRegex(replay.MissingEvidence, "public evidence missing"):
            replay.replay(self.data)

    def test_missing_source_evidence_is_not_an_empty_module(self):
        del self.data["sources"]["VerifiedGarbage.B"]
        with self.assertRaisesRegex(replay.MissingEvidence, "source of VerifiedGarbage.B"):
            replay.replay(self.data)

    def test_incompatible_snapshot_version_is_rejected(self):
        self.data["schema"] = 9000
        with self.assertRaisesRegex(ValueError, "schema"):
            replay.replay(self.data)

    def test_independent_discovery_finds_what_shake_misses(self):
        self.data["shake"] = {m: [[], []] for m in self.data["selected"]}
        self.assertFalse(replay.replay(self.data)["edits"])
        self.assertEqual(len(replay.replay(self.data, independent=True)["edits"]), 3)

    def test_independent_discovery_respects_explicit_keep(self):
        for m in self.data["selected"]:
            self.data["sources"][m]["text"] = "module\npublic import VerifiedGarbage.B -- shake: keep\n"
        self.assertFalse(replay.replay(self.data, independent=True)["edits"])

    def test_discovery_explains_used_imports_even_when_no_hypothesis_is_generated(self):
        self.data["uses"]["public"]["VerifiedGarbage.A"] = ["VerifiedGarbage.B"]
        self.data["sources"]["VerifiedGarbage.C"]["text"] = "module\nimport VerifiedGarbage.B\n"
        self.data["shake"] = {m: [[], []] for m in self.data["selected"]}
        result = replay.replay(self.data, independent=True)
        decisions = {d["module"]: d for d in result["decisions"] if d["dependency"] == "VerifiedGarbage.B"}
        self.assertEqual(decisions["VerifiedGarbage.A"]["reason"], "public_declaration_dependency")
        self.assertEqual(decisions["VerifiedGarbage.C"]["reason"], "direct_private_dependency")
        self.assertEqual({d["status"] for d in decisions.values()}, {"retained"})

    def meta_fixture(self):
        for mod in self.data["selected"]:
            self.data["sources"][mod]["text"] = "module\nmeta import VerifiedGarbage.B\n"
            self.data["shake"][mod] = [[], []]
            for view in self.data["uses"]:
                self.data["uses"][view][mod] = []

    def test_private_meta_discovery_replays_without_lean_and_obeys_the_budget(self):
        self.meta_fixture()
        with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")), \
                mock.patch.object(check.subprocess, "Popen", side_effect=AssertionError("no processes")):
            result = replay.replay(self.data, independent=True, max_affected=2)
        self.assertEqual(result["edits"], [{"module": "VerifiedGarbage.A", "action": "remove_meta",
                                           "dependency": "VerifiedGarbage.B"}])
        self.assertEqual(result["cost"]["affected_modules"], 2)
        self.assertEqual(result["deferred"][0]["module"], "VerifiedGarbage.C")
        self.assertEqual(result["visibility_impact"]["totals"]["meta_reads"]["removed_pairs"], 1)
        self.assertFalse(result["build_verified"])

    def test_private_meta_discovery_requires_its_phase_evidence(self):
        self.meta_fixture()
        del self.data["uses"]["meta_private"]["VerifiedGarbage.A"]
        with self.assertRaisesRegex(replay.MissingEvidence, "meta_private evidence missing"):
            replay.replay(self.data, independent=True)

    def test_private_meta_discovery_reports_direct_retention(self):
        self.meta_fixture()
        for mod in self.data["selected"]:
            self.data["uses"]["meta_private"][mod] = ["VerifiedGarbage.B"]
        result = replay.replay(self.data, independent=True)
        self.assertFalse(result["edits"])
        self.assertEqual({d["reason"] for d in result["decisions"]}, {"direct_meta_dependency"})

    def empty_namespace_fixture(self):
        self.data["selected"] = ["VerifiedGarbage.A"]
        self.data["sources"]["VerifiedGarbage.A"]["text"] = (
            "module\nimport VerifiedGarbage.B\nopen UnrecordedNamespace73129\n")
        self.data["sources"]["VerifiedGarbage.B"]["text"] = (
            "module\npublic section\nnamespace UnrecordedNamespace73129\nend UnrecordedNamespace73129\n")
        self.data["shake"] = {"VerifiedGarbage.A": [["import VerifiedGarbage.B"], []]}
        for view in self.data["uses"]:
            self.data["uses"][view]["VerifiedGarbage.A"] = []
        self.data["uses"]["namespace_exports"] = {"VerifiedGarbage.B": ["UnrecordedNamespace73129"]}

    def test_empty_namespace_registration_is_replayed_as_a_source_dependency(self):
        self.empty_namespace_fixture()
        with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")):
            result = replay.replay(self.data)
        self.assertFalse(result["edits"])
        self.assertEqual(result["decisions"][0]["reason"], "source_dependency")

    def test_empty_namespace_registration_requires_captured_evidence(self):
        self.empty_namespace_fixture()
        del self.data["uses"]["namespace_exports"]
        with self.assertRaisesRegex(replay.MissingEvidence, "namespace_exports evidence missing"):
            replay.replay(self.data)

    def test_raw_shake_evidence_is_not_mutated_by_discovery(self):
        before = copy.deepcopy(self.data)
        replay.replay(self.data, independent=True)
        self.assertEqual(self.data, before)

    def test_partial_reader_output_stops_capture(self):
        evidence = replay.Evidence(lambda mods, view: {}, 2)
        with self.assertRaisesRegex(replay.MissingEvidence, "not returned"):
            evidence(["VerifiedGarbage.A"], "public")

    def test_reader_batches_and_reuses_queries(self):
        calls = []
        def read(mods, view):
            calls.append(list(mods))
            return {m: {"X"} for m in mods}
        evidence = replay.Evidence(read, 2)
        evidence(["C", "A", "B"], "names")
        evidence(["A", "C"], "names")
        self.assertEqual(calls, [["A", "B"], ["C"]])

    def test_effect_metadata_batches_files_independently_of_environment_roots(self):
        calls = []
        def read(mods, view):
            calls.append((list(mods), view))
            return {m: set() for m in mods}
        evidence = replay.Evidence(read, 2)
        modules = [f"M{i:02}" for i in range(67)]
        evidence(modules, "effects")
        evidence(modules[:4], "effects")
        self.assertEqual([len(mods) for mods, _ in calls], [32, 32, 3])
        self.assertEqual({view for _, view in calls}, {"effects"})

    def test_capture_roundtrip_uses_only_consulted_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            lean = root / "lean"
            for mod, source in self.data["sources"].items():
                p = lean.joinpath(*mod.split(".")).with_suffix(".lean")
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(source["text"])
            with mock.patch.object(check, "LEAN", lean), mock.patch.object(check, "ROOT", root):
                graph = check.Graph([lean])
                graph.users = check.reverse_index(self.data["library"])
                evidence = replay.Evidence(lambda ms, view: {m: set(self.data["uses"][view][m]) for m in ms}, 2)
                shaken = {str(check.graph_path(m)): v for m, v in self.data["shake"].items()}
                plan = check.analyze(self.data["selected"], shaken, graph, uses=evidence, library=self.data["library"])
                expected = replay.report(plan, replay.cost(plan, graph, self.data["library"], {}), graph)
                captured = replay.capture(self.data["selected"], self.data["library"], graph, shaken, evidence, {}, False)
            # The original files and root aren't needed at replay time.
        self.assertEqual(replay.replay(json.loads(json.dumps(captured))), expected)

    def test_cli_replay_writes_an_unverified_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "report.json"
            with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no processes")):
                self.assertEqual(trim.main(["--replay", str(FIXTURE), "--report", str(path)]), 0)
            self.assertFalse(json.loads(path.read_text())["build_verified"])

    def test_absent_profiles_are_counted_without_inventing_times(self):
        self.data["profile"] = {}
        result = replay.replay(self.data)
        self.assertEqual(result["cost"]["unprofiled_modules"], 3)
        self.assertEqual(result["cost"]["known_profile_work_seconds"], 0)

    def test_cli_capture_does_not_edit_or_verify_proposals(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            lean = root / "lean"
            for mod, source in self.data["sources"].items():
                p = lean.joinpath(*mod.split(".")).with_suffix(".lean")
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(source["text"])
            snapshot = root / "capture.json"
            report = root / "report.json"
            with mock.patch.object(check, "LEAN", lean), mock.patch.object(check, "ROOT", root), \
                    mock.patch.object(trim, "STATE", root / "state.json"), \
                    mock.patch.object(check, "dependency_roots", return_value=[lean]), \
                    mock.patch.object(check, "build_modules"), \
                    mock.patch.object(check, "shake", side_effect=AssertionError("shake disabled")), \
                    mock.patch.object(check, "module_uses", side_effect=lambda ms, v: {
                        m: set(self.data["uses"][v][m]) for m in ms}), \
                    mock.patch.object(check, "module_evidence", side_effect=lambda ms, *args: {
                        m: {v: set(self.data["uses"][v][m]) for v in check.DECLARATION_VIEWS} for m in ms}), \
                    mock.patch.object(check, "fix_and_verify", side_effect=AssertionError("no verification")):
                self.assertEqual(trim.main(["-m", *self.data["selected"], "--discover", "--no-shake",
                                            "--capture", str(snapshot), "--report", str(report)]), 0)
            self.assertEqual(replay.replay(json.loads(snapshot.read_text())), json.loads(report.read_text()))
            for mod, source in self.data["sources"].items():
                self.assertEqual(lean.joinpath(*mod.split(".")).with_suffix(".lean").read_text(), source["text"])

    def test_rejected_live_plan_saves_replayable_pre_edit_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            lean = root / "lean"
            for mod, source in self.data["sources"].items():
                path = lean.joinpath(*mod.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source["text"])
            def reject(plan, library, **kwargs):
                kwargs["audit"].update(status="rejected", build_verified=False)
                return [], ["VerifiedGarbage.A"]
            audit = {}
            with mock.patch.object(check, "LEAN", lean), mock.patch.object(check, "ROOT", root), \
                    mock.patch.object(check, "dependency_roots", return_value=[lean]), \
                    mock.patch.object(trim, "shaken", return_value={str(lean.joinpath(*m.split('.')).with_suffix('.lean')): v
                                                               for m, v in self.data["shake"].items()}), \
                    mock.patch.object(trim, "cached_uses", return_value=lambda ms, view: {
                        m: set(self.data["uses"][view][m]) for m in ms}), \
                    mock.patch.object(check, "fix_and_verify", side_effect=reject):
                trim.trim(self.data["selected"], self.data["library"], 1, 2,
                          trim.State(root / "state.json"), audit=audit)
                path = pathlib.Path(audit["rounds"][0]["rejection_evidence"])
                captured = replay.load(path)
                with mock.patch.object(check.subprocess, "run", side_effect=AssertionError("no Lean")):
                    replanned = replay.replay(captured)
                self.assertEqual(replanned["edits"], audit["rounds"][0]["plan"]["edits"])
                self.assertEqual(captured["verification"]["status"], "rejected")

    def test_profile_work_excludes_blocked_time(self):
        with tempfile.TemporaryDirectory() as tmp:
            lean = pathlib.Path(tmp)
            p = lean / ".lake/build/lib/lean/VerifiedGarbage/A.trace"
            p.parent.mkdir(parents=True)
            p.write_text(json.dumps({"log": [
                {"level": "info", "message": "A.lean:1:0: type checking took 100ms"},
                {"level": "info", "message": "A.lean:1:0: simp took 200ms"},
                {"level": "info", "message": "A.lean:1:0: blocked took 10s"},
            ]}))
            with mock.patch.object(check, "LEAN", lean):
                result = replay.profile_cost(["VerifiedGarbage.A", "VerifiedGarbage.Missing"])
            self.assertAlmostEqual(result["VerifiedGarbage.A"], 0.3)
            self.assertNotIn("VerifiedGarbage.Missing", result)


if __name__ == "__main__":
    unittest.main()
