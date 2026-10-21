"""The bulk import trim's rounds, cache and state, with the check stubbed;
no builds."""

import json
import pathlib
import tempfile
import unittest
from unittest import mock

import check_lean_public_imports as check
import trim_lean_imports as trim


class Trim(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.lean = self.root / "lean"
        for target, value in ((check, "LEAN"), (check, "ROOT")):
            patch = mock.patch.object(target, value, self.lean if value == "LEAN" else self.root)
            patch.start()
            self.addCleanup(patch.stop)
        source = self.lean / "VerifiedGarbage/A.lean"
        source.parent.mkdir(parents=True)
        source.write_text("module\nimport VerifiedGarbage.B\n")
        self.trace("VerifiedGarbage.A", "aaaa")
        self.state = trim.State(self.root / "state.json")

    def trace(self, mod, dep):
        p = self.lean / ".lake/build/lib/lean" / pathlib.Path(*mod.split(".")).with_suffix(".trace")
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps({"depHash": dep, "outputs": {"o": [f"{dep}.olean"]}}))

    def test_the_key_is_lakes_hash_of_inputs_and_outputs(self):
        before = trim.trace_key("VerifiedGarbage.A")
        self.assertIsNotNone(before)
        path = self.lean / ".lake/build/lib/lean/VerifiedGarbage/A.trace"
        data = json.loads(path.read_text())
        data["outputs"]["private"] = ["changed.olean.private"]
        path.write_text(json.dumps(data))
        self.assertNotEqual(before, trim.trace_key("VerifiedGarbage.A"))
        self.assertIsNone(trim.trace_key("VerifiedGarbage.Unbuilt"))

    def test_an_unchanged_module_is_not_shaken_again(self):
        path = str(check.graph_path("VerifiedGarbage.A"))
        out = f"{path}:\n  remove #[import VerifiedGarbage.B]\n"
        with mock.patch.object(check, "build_modules"), mock.patch.object(check, "shake", return_value=out) as shake:
            self.assertEqual(trim.shaken(["VerifiedGarbage.A"], self.state, 10),
                             {path: (["import VerifiedGarbage.B"], [])})
            trim.shaken(["VerifiedGarbage.A"], trim.State(self.state.path), 10)
            self.assertEqual(shake.call_count, 1)
            # A new build of A: shaken again.
            self.trace("VerifiedGarbage.A", "bbbb")
            trim.shaken(["VerifiedGarbage.A"], trim.State(self.state.path), 10)
            self.assertEqual(shake.call_count, 2)

    def test_uses_are_cached_by_build(self):
        with mock.patch.object(check, "build_modules"), \
                mock.patch.object(check, "module_evidence", return_value={"VerifiedGarbage.A": {
                    "public": {"X"}, "private": {"Y"}, "meta_public": set(), "meta_private": set()}}) as read:
            uses = trim.cached_uses(self.state)
            self.assertEqual(uses(["VerifiedGarbage.A"], "public"), {"VerifiedGarbage.A": {"X"}})
            self.assertEqual(uses(["VerifiedGarbage.A"], "public"), {"VerifiedGarbage.A": {"X"}})
            self.assertEqual(uses(["VerifiedGarbage.A"], "private"), {"VerifiedGarbage.A": {"Y"}})
            self.assertEqual(read.call_count, 1)

    def test_a_persistent_cache_hit_still_warms_the_downstream_root(self):
        views = {"public": {"X"}, "private": {"Y"}, "meta_public": set(), "meta_private": set()}
        with mock.patch.object(check, "build_modules"), \
                mock.patch.object(check, "module_evidence", return_value={"VerifiedGarbage.A": views}):
            trim.cached_uses(self.state)(["VerifiedGarbage.A"], "public")
        state = trim.State(self.state.path)
        with mock.patch.object(check, "build_modules") as build, \
                mock.patch.object(check, "module_evidence", side_effect=AssertionError("cached")):
            uses = trim.cached_uses(state)
            self.assertEqual(uses(["VerifiedGarbage.A"], "private"), {"VerifiedGarbage.A": {"Y"}})
            uses(["VerifiedGarbage.A"], "public")
        build.assert_called_once_with(["VerifiedGarbage.A"], None)

    def test_source_body_change_invalidates_uses_even_before_a_new_trace(self):
        views = {v: set() for v in check.DECLARATION_VIEWS}
        with mock.patch.object(check, "build_modules") as build, \
                mock.patch.object(check, "module_evidence", return_value={"VerifiedGarbage.A": views}) as read:
            uses = trim.cached_uses(self.state)
            uses(["VerifiedGarbage.A"], "public")
            path = check.graph_path("VerifiedGarbage.A")
            path.write_text(path.read_text() + "def changed : Nat := 1\n")
            uses(["VerifiedGarbage.A"], "public")
        self.assertEqual(build.call_count, 2)
        self.assertEqual(read.call_count, 2)

    def test_no_shake_mode_only_checks_selected_builds(self):
        with mock.patch.object(check, "build_modules") as build, mock.patch.object(check, "shake") as shake:
            self.assertEqual(trim.shaken(["VerifiedGarbage.A"], self.state, 10, skip=True),
                             {str(check.graph_path("VerifiedGarbage.A")): ([], [])})
        build.assert_called_once_with(["VerifiedGarbage.A"])
        shake.assert_not_called()

    def test_incomplete_reader_does_not_reuse_stale_cached_uses(self):
        self.state.uses = {"public": {"VerifiedGarbage.A": ["old", ["Stale"]]}}
        with mock.patch.object(check, "build_modules"), mock.patch.object(check, "module_evidence", return_value={}):
            with self.assertRaisesRegex(trim.replay.MissingEvidence, "omitted"):
                trim.cached_uses(self.state)(["VerifiedGarbage.A"], "public")

    def test_planner_changes_retain_raw_evidence_and_clear_rejections(self):
        self.state.shake = {"VerifiedGarbage.A": ["old", [], []]}
        self.state.undone.add("old rejection")
        self.state.save()
        with mock.patch.object(trim.replay, "analyzer_key", return_value="new analyzer"):
            state = trim.State(self.state.path)
        self.assertTrue(state.shake)
        self.assertFalse(state.undone)

    def test_budget_defers_the_entire_dependent_batch(self):
        path = self.lean / "VerifiedGarbage/D.lean"
        path.write_text("module\nimport VerifiedGarbage.A\n")
        plan = check.Plan(edits=[check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B")])
        with mock.patch.object(trim, "shaken", return_value={}), \
                mock.patch.object(check, "dependency_roots", return_value=[]), \
                mock.patch.object(check, "analyze", return_value=plan), \
                mock.patch.object(check, "fix_and_verify") as fix:
            result = trim.trim(["VerifiedGarbage.A"], ["VerifiedGarbage.A", "VerifiedGarbage.D"],
                               1, 10, self.state, max_affected=1)
        fix.assert_not_called()
        self.assertEqual(result["applied"], 0)

    def run_rounds(self, findings, fixes):
        with mock.patch.object(trim, "shaken", return_value={}), \
                mock.patch.object(check, "dependency_roots", return_value=[]), \
                mock.patch.object(check, "analyze", side_effect=[check.Plan(
                    edits=[check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B")] if f else []) for f in findings]), \
                mock.patch.object(check, "fix_and_verify", side_effect=fixes) as fix:
            return trim.trim(["VerifiedGarbage.A"], ["VerifiedGarbage.A"], 5, 10, self.state), fix

    def test_rounds_stop_when_nothing_is_left(self):
        f = "lean/VerifiedGarbage/A.lean:4: `import VerifiedGarbage.B`: VerifiedGarbage.A does not use it: remove it"
        totals, fix = self.run_rounds([[f], []], [(["lean/VerifiedGarbage/A.lean: remove VerifiedGarbage.B"], [])])
        self.assertEqual(totals, {"rounds": 2, "applied": 1, "undone": 0})
        self.assertEqual(fix.call_count, 1)

    def test_an_undone_finding_is_not_tried_again(self):
        f = "lean/VerifiedGarbage/A.lean:4: `import VerifiedGarbage.B`: VerifiedGarbage.A does not use it: remove it"
        # Round 1 undoes it; round 2 finds it again and skips it: no progress.
        totals, fix = self.run_rounds([[f], [f]], [([], ["VerifiedGarbage.A"])])
        self.assertEqual(totals["undone"], 1)
        self.assertEqual(fix.call_count, 1)
        self.assertEqual(len(trim.State(self.state.path).undone), 1)
        # A separate run with identical evidence performs no verification.
        _, fix = self.run_rounds([[f]], [])
        fix.assert_not_called()
        # Changed inputs reopen the experiment.
        self.trace("VerifiedGarbage.A", "changed")
        _, fix = self.run_rounds([[f]], [([], ["VerifiedGarbage.A"])])
        fix.assert_called_once()

    def test_an_unrelated_success_does_not_reopen_a_failed_file_trial(self):
        path = self.lean / "VerifiedGarbage/C.lean"
        path.write_text("module\nimport VerifiedGarbage.B\n")
        mods = ["VerifiedGarbage.A", "VerifiedGarbage.C"]
        def analyze(selected, *args, **kwargs):
            return check.Plan(edits=[check.Edit(m, "remove", "VerifiedGarbage.B") for m in selected
                                     if "import VerifiedGarbage.B" in check.graph_path(m).read_text()])
        def partial(plan, library, **kwargs):
            path.write_text("module\n")
            kwargs["audit"].update(status="verified", build_verified=True)
            return ["lean/VerifiedGarbage/C.lean: remove VerifiedGarbage.B"], ["VerifiedGarbage.A"]
        with mock.patch.object(trim, "shaken", return_value={}), \
                mock.patch.object(check, "dependency_roots", return_value=[self.lean]), \
                mock.patch.object(check, "analyze", side_effect=analyze), \
                mock.patch.object(check, "fix_and_verify", side_effect=partial) as verify:
            result = trim.trim(mods, mods, 3, 4, self.state)
        self.assertEqual(result, {"rounds": 2, "applied": 1, "undone": 1})
        self.assertEqual(verify.call_count, 1)
        self.assertTrue(trim.State(self.state.path).module_rejections["VerifiedGarbage.A"])

    def test_planned_upstream_edits_reopen_a_trial_but_unrelated_edits_do_not(self):
        for name in ("B", "C", "D"):
            check.graph_path("VerifiedGarbage." + name).write_text("module\n")
        graph = check.Graph([self.lean])
        mods = ["VerifiedGarbage." + x for x in "ABCD"]
        context = trim.trial_context(mods, graph)
        own = check.Edit("VerifiedGarbage.A", "remove", "VerifiedGarbage.B")
        key = lambda edits: trim.module_trial_key("VerifiedGarbage.A", check.Plan(edits=edits), graph, mods, context)
        baseline = key([own])
        self.assertEqual(baseline, key([own, check.Edit("VerifiedGarbage.C", "add", "VerifiedGarbage.D")]))
        self.assertNotEqual(baseline, key([own, check.Edit("VerifiedGarbage.B", "add", "VerifiedGarbage.D")]))
        # C enters A's dependencies only through a planned edge. Its own
        # planned changes must still invalidate A's rejection context.
        added = check.Edit("VerifiedGarbage.A", "add", "VerifiedGarbage.C")
        self.assertNotEqual(key([own, added]), key([own, added, check.Edit("VerifiedGarbage.C", "add", "VerifiedGarbage.D")]))
        self.assertEqual(key([own, added]), key([added, own]))
        consumer = check.Edit("VerifiedGarbage.D", "add", "VerifiedGarbage.A")
        before = key([own, consumer])
        context["traces"]["VerifiedGarbage.D"] = "a changed new consumer"
        self.assertNotEqual(before, key([own, consumer]))

    def test_explicit_retry_retains_raw_evidence_caches(self):
        self.state.shake = {"VerifiedGarbage.A": ["old", [], []]}
        self.state.undone = {"old batch"}
        self.state.module_rejections = {"VerifiedGarbage.A": {"old trial": {"manifest": "old.json"}}}
        self.state.save()
        with mock.patch.object(trim, "STATE", self.state.path), \
                mock.patch.object(trim, "trim", return_value={"rounds": 1, "applied": 0, "undone": 0}):
            self.assertEqual(trim.main(["-m", "VerifiedGarbage.A", "--retry-rejected"]), 0)
        state = trim.State(self.state.path)
        self.assertTrue(state.shake)
        self.assertFalse(state.undone)
        self.assertFalse(state.module_rejections)


if __name__ == "__main__":
    unittest.main()
