"""The run's metrics (ci_metrics.py) from its jobs and their logs; no API."""

import json
import io
import os
import pathlib
import subprocess
import tempfile
import unittest
import zipfile
from unittest import mock

import ci_metrics

KEY = "lean-build-Linux-X64-a-b"


def step(name, start, end):
    return {"name": name, "conclusion": "success",
            "started_at": f"2026-10-07T12:{start}Z", "completed_at": f"2026-10-07T12:{end}Z"}


def api_job(name, start, end, steps=()):
    return {"name": name, "conclusion": "success", "runner_name": "r", "labels": ["ubuntu-latest"],
            "created_at": "2026-10-07T12:00:00Z", "started_at": f"2026-10-07T12:{start}Z",
            "completed_at": end and f"2026-10-07T12:{end}Z", "steps": list(steps)}


def line(at, text):
    return f"2026-10-07T12:{at}.1234567Z {text}\n"


PLAN_LOG = (line("00:30", "Cache restored from key: lean-manifest-Linux-X64-a-b")
            + line("00:31", "1168 modules to build, about 7208 s; shards' estimated times: [508, 285]"))
SHARD_BUILD = "Check the shard's proofs (and the axiom audit)"
ASSEMBLE = "Run ./.github/actions/lean-assemble"


class PlanOf(unittest.TestCase):
    def test_the_plan_lean_reuse_chose(self):
        log = (PLAN_LOG + line("00:32", "12 modules to build, about 36 s; shards' estimated times: []")
               + line("00:32", "The plan builds on lean-build-Linux-X64-a-c."))
        self.assertEqual(ci_metrics.plan_of(log), {"stale": 12, "work": 36, "estimates": [],
                                                   "build": "lean-build-Linux-X64-a-c"})

    def test_a_plan_of_lean_shards(self):
        self.assertEqual(ci_metrics.plan_of(PLAN_LOG)["build"], KEY)


class Collect(unittest.TestCase):
    jobs = [
        api_job("Lean: plan and build", "00:10", "00:40"),
        api_job("Lean: shard (1)", "01:00", "09:00",
                [step("Run ./.github/actions/lean-prepare", "01:00", "02:00"),
                 step(SHARD_BUILD, "02:00", "04:00"), step(ASSEMBLE, "04:01", "09:00")]),
        api_job("Lean: shard (2)", "01:00", "03:00", [step(SHARD_BUILD, "02:00", "02:30")]),
        api_job("Coverage", "00:10", None),
    ]
    logs = {
        "Lean: plan and build": PLAN_LOG,
        # Its restore failed: it restored no build.
        "Lean: shard (1)": (line("01:10", f"  key: {KEY}") + line("01:50", "##[warning]Failed to restore")
                            + line("03:00", "✔ [1/9] Built VerifiedGarbage.A (3s)")
                            + line("03:10", "✔ [2/9] Built VerifiedGarbage.A:c.o (9s)")
                            + line("03:59", "✔ [3/9] Built VerifiedGarbage.B (500ms)")
                            # In the assembly: a step of its own.
                            + line("05:00", "✔ [4/9] Built VerifiedGarbage.C (2s)")),
        "Lean: shard (2)": (line("01:10", f"  key: {KEY}") + line("01:20", f"Cache restored from key: {KEY}")
                            + line("02:10", "✔ [1/9] Built VerifiedGarbage.A (2s)")),
    }

    def metrics(self):
        return ci_metrics.collect({"id": 7, "event": "pull_request", "base_ref": "main"}, self.jobs, self.logs)

    def test_plan(self):
        self.assertEqual(self.metrics()["lean"]["plan"],
                         {"stale": 1168, "work": 7208, "estimates": [508, 285], "build": KEY})

    def test_builds_by_step(self):
        one, two = [j for j in self.metrics()["lean"]["jobs"] if j["name"].startswith("Lean: shard")]
        # A facet's line (`A:c.o`) is not a module's.
        self.assertEqual(one["built"], {SHARD_BUILD: {"VerifiedGarbage.A": 3.0, "VerifiedGarbage.B": 0.5},
                                        ASSEMBLE: {"VerifiedGarbage.C": 2.0}})
        self.assertEqual((one["restored"], one["restored_planned"]), (None, False))
        self.assertEqual((two["restored"], two["restored_planned"]), (KEY, True))
        # A was built by both shards: the cheaper build counts as duplicate.
        self.assertEqual(self.metrics()["lean"]["duplicate_work"], 2.0)

    def test_jobs(self):
        m = self.metrics()
        self.assertEqual(m["run"]["base_ref"], "main")
        shard = m["jobs"][1]
        self.assertEqual((shard["queued_s"], shard["duration_s"]), (60, 480))
        # A job still running has no duration.
        self.assertIsNone(m["jobs"][3]["duration_s"])

    def test_native_facets_are_retained_separately_from_proofs(self):
        one = self.metrics()["lean"]["jobs"][1]
        self.assertEqual(one["facets"], {SHARD_BUILD: {"VerifiedGarbage.A:c.o": 9.0}})
        self.assertEqual(one["phases"], {"queued_s": 60, "prepare_s": 60, "proof_s": 120,
                                        "unpack_s": None, "assemble_s": 299, "planning_s": None})
        self.assertIn("### Lean wall time by phase", ci_metrics.summary(self.metrics()))

    def test_missing_logs_are_explicit(self):
        m = ci_metrics.collect({}, self.jobs, {"Lean: plan and build": PLAN_LOG})
        self.assertEqual(m["lean"]["missing_logs"], ["Lean: shard (1)", "Lean: shard (2)"])
        self.assertIn("Missing job logs", ci_metrics.summary(m))

    def test_build_at_a_step_boundary_belongs_to_the_new_step(self):
        steps = [step("Restore", "01:00", "02:00"), step(SHARD_BUILD, "02:00", "03:00")]
        log = line("02:00", "Built A (20ms)") + line("02:00", "Built A:c.o (50ms)")
        self.assertEqual(ci_metrics.built_by_step(log, steps), {SHARD_BUILD: {"A": 0.02}})
        self.assertEqual(ci_metrics.built_by_step(log, steps, facets=True), {SHARD_BUILD: {"A:c.o": 0.05}})

    def test_summary(self):
        text = ci_metrics.summary(self.metrics())
        self.assertIn("Plan: 1168 modules to build, about 7208 s of work, 2 shards.", text)
        self.assertIn(f"| Lean: shard (1) | {SHARD_BUILD} | 508 s | 120 s | 2 | 4 s | **no** (none) |", text)
        self.assertIn(f"| Lean: shard (1) | {ASSEMBLE} | – | 299 s | 1 | 2 s | **no** (none) |", text)
        self.assertIn(f"| Lean: shard (2) | {SHARD_BUILD} | 285 s | 30 s | 1 | 2 s | yes |", text)
        self.assertIn("| Lean: shard (1) | 60 s | 480 s |", text)

    def test_without_a_lean_build(self):
        m = ci_metrics.collect({"id": 7}, [api_job("Coverage", "00:10", "01:00")], {})
        self.assertIsNone(m["lean"]["plan"])
        self.assertIn("No plan", ci_metrics.summary(m))


class RustTimings(unittest.TestCase):
    def test_tests_keep_step_binary_feature_context_and_repeated_names(self):
        j = api_job("Rust (sde -icx)", "00:00", "01:00",
                    [step("Test the implementations", "00:00", "00:40"),
                     step("Other tests", "00:40", "01:00")])
        j["id"] = 42
        log = (line("00:01", "##[group]VG_CPU_FEATURES=avx: rsa")
               + line("00:02", "     Running unittests src/lib.rs (target/debug/deps/vg-abc)")
               + line("00:02", "running 2 tests")
               + line("00:03", "test rsa::sign ... \x1b[32mok\x1b[0m <0.123s>")
               + line("00:04", "test rsa::untimed ... ok")
               + line("00:05", "     Running tests/main.rs (target/debug/deps/tests-def)")
               + line("00:05", "running 1 test")
               + line("00:06", "test rsa::sign ... FAILED <1.234s>")
               + line("00:07", "##[endgroup]")
               + line("00:08", "VG_CPU_FEATURES=avx: rsa: 2.100 0.200 s of CPU (user, system)")
               + line("00:09", "CI_FEATURE_TIME_V1 0 2000000 5500000 1000000 1")
               + line("00:41", "test rsa::sign ... ok <0.003s>"))
        m = ci_metrics.collect({}, [j], {j["name"]: log})
        r = m["rust"]["jobs"][0]
        self.assertEqual(r["job_id"], 42)
        self.assertEqual(len(r["tests"]), 3)
        self.assertEqual([t["elapsed_s"] for t in r["tests"]], [0.123, 1.234, 0.003])
        self.assertEqual(r["tests"][0]["feature_line"], "VG_CPU_FEATURES=avx: rsa")
        self.assertIn("tests/main.rs", r["tests"][1]["binary"])
        self.assertEqual(r["tests"][1]["outcome"], "FAILED")
        self.assertIsNone(r["tests"][2]["feature_line"])
        self.assertIsNone(r["tests"][2]["binary"])
        self.assertEqual(r["feature_runs"], [{"features": "avx", "groups": ["rsa"],
                         "user_s": 2.1, "system_s": 0.2, "start_offset_s": 1.0,
                         "wall_s": 3.5, "exit_code": 1}])
        self.assertEqual(m["lean"]["jobs"], [])
        self.assertIn("## Rust timings", ci_metrics.summary(m))

    def test_buffered_stdout_uses_command_boundaries_and_ordered_binaries(self):
        j = ci_metrics.job(api_job("Rust (Windows)", "00:00", "01:00",
                    [step("Run rustc -vV", "00:00", "00:00"),
                     step("Tests", "00:00", "00:40"), step("Export coverage", "00:40", "01:00")]))
        log = (line("00:00", "##[group]Run cargo test")
               + line("00:00", "##[endgroup]")
               + line("00:01", "     Running unittests src\\lib.rs (lib.exe)")
               + line("00:02", "     Running tests\\main.rs (tests.exe)")
               + line("00:03", "   Doc-tests vg")
               + line("00:40", "running 1 test")
               + line("00:40", "test a ... ok <0.001s>")
               + line("00:40", "running 1 test")
               + line("00:40", "test b ... ok <0.002s>")
               + line("00:40", "running 0 tests")
               + line("00:40", "##[group]Run export coverage"))
        tests = ci_metrics.rust_metrics(j, log)["tests"]
        self.assertEqual([t["step"] for t in tests], ["Tests", "Tests"])
        self.assertIn("lib.exe", tests[0]["binary"])
        self.assertIn("tests.exe", tests[1]["binary"])

    def test_old_logs_and_invalid_wall_record_do_not_imply_zero(self):
        j = ci_metrics.job(api_job("Rust (native)", "00:00", "01:00"))
        cpu = line("00:01", "VG_CPU_FEATURES=: all: 1.000 0.000 s of CPU (user, system)")
        for record in ("", "CI_FEATURE_TIME_V1 0 4 3 1 0", "CI_FEATURE_TIME_V1 5 2 3 1 0"):
            r = ci_metrics.rust_metrics(j, cpu + line("00:02", record))
            self.assertEqual(r["tests"], [])
            self.assertIsNone(r["feature_runs"][0]["wall_s"])
            self.assertEqual(r["feature_runs"][0]["groups"], ["all"])

    def test_collection_is_explicitly_incomplete_and_excludes_skipped_durations(self):
        done = dict(api_job("Rust (native)", "00:00", "01:00"), id=1)
        skipped = dict(api_job("Lean: shard", "00:01", "00:00"), id=2, conclusion="skipped")
        active = dict(api_job("all-green", "01:00", None), id=3)
        c = ci_metrics.collect({}, [done, skipped, active], {})["collection"]
        self.assertEqual(c["finished_runner_s"], 60)
        self.assertFalse(c["jobs_complete"])
        self.assertEqual(c["unfinished_job_ids"], [3])
        self.assertEqual(c["missing_log_job_ids"], [1])

    def test_legacy_summary_still_works(self):
        m = ci_metrics.collect({}, [], {})
        del m["rust"], m["collection"]
        self.assertIn("No plan", ci_metrics.summary(m))

    def test_requests_share_deadline(self):
        with mock.patch.object(ci_metrics, "COLLECT_DEADLINE", 100), \
                mock.patch.object(ci_metrics.time, "monotonic", return_value=98), \
                mock.patch.object(ci_metrics.subprocess, "run") as run:
            ci_metrics.gh("repos/o/r")
        self.assertEqual(run.call_args.kwargs["timeout"], 2)

    def test_main_push_does_not_fetch_rust_logs(self):
        j = dict(api_job("Rust (native)", "00:00", "01:00"), id=1, status="completed")
        def gh(path, *args):
            self.assertNotIn("/logs", path)
            if "/jobs?" in path:
                return json.dumps(j).encode()
            if "/artifacts?" in path:
                return b'{"artifacts": []}'
            return b'{"id": 7, "event": "push"}'
        env = {"GH_REPO": "o/r", "GITHUB_RUN_ID": "7", "GITHUB_RUN_ATTEMPT": "1"}
        with mock.patch.object(ci_metrics, "gh", gh), mock.patch.dict(os.environ, env):
            m = ci_metrics.collect_this_run()
        self.assertEqual(m["rust"]["jobs"], [])
        self.assertEqual(m["collection"]["missing_log_job_ids"], [])

    def test_missing_rust_log_does_not_discard_other_observations(self):
        jobs = [dict(api_job("Rust (native)", "00:00", "01:00"), id=1, status="completed"),
                dict(api_job("Rust (other)", "00:00", "01:00"), id=2, status="completed")]
        def gh(path, *args):
            if "/jobs/1/logs" in path:
                return line("00:01", "test a ... ok <0.005s>").encode()
            if "/jobs/2/logs" in path:
                raise subprocess.TimeoutExpired("gh", 5)
            if "/jobs?" in path:
                return "\n".join(map(json.dumps, jobs)).encode()
            if "/artifacts?" in path:
                return b'{"artifacts": []}'
            return b'{"id": 7}'
        env = {"GH_REPO": "o/r", "GITHUB_RUN_ID": "7", "GITHUB_RUN_ATTEMPT": "1"}
        with mock.patch.object(ci_metrics, "gh", gh), mock.patch.dict(os.environ, env), \
                mock.patch("sys.stderr"):
            m = ci_metrics.collect_this_run()
        self.assertEqual(m["rust"]["jobs"][0]["tests"][0]["elapsed_s"], 0.005)
        self.assertEqual(m["collection"]["missing_log_job_ids"], [2])
        self.assertIsNone(ci_metrics.COLLECT_DEADLINE)


class Standalone(unittest.TestCase):
    def test_built_is_lean_shards(self):
        # CI fetches ci_metrics.py alone: it keeps its own copy.
        import lean_shards
        self.assertEqual(ci_metrics.BUILT.pattern, lean_shards.BUILT.pattern)


class CollectThisRun(unittest.TestCase):
    def test_a_missing_log(self):
        # The plan's log comes (after asking again); a skipped shard's does not.
        def gh(path, *args):
            if path.endswith("/jobs/2/logs"):
                raise subprocess.CalledProcessError(1, "gh", stderr=b"HTTP 404")
            if path.endswith("/jobs/1/logs"):
                # As newer `gh` does for a log with terminal colors.
                if "--allow-escape-sequences" not in args:
                    raise subprocess.CalledProcessError(1, "gh", stderr=b"the response contains terminal escape "
                                                        b"sequences; pass --allow-escape-sequences to output it anyway")
                return PLAN_LOG.encode()
            if "/jobs?" in path:
                return "\n".join(json.dumps(dict(j, id=i, status="completed")) for i, j in enumerate(
                    [api_job("Lean: plan and build", "00:10", "00:40"), api_job("Lean: shard (1)", "01:00", "02:00")],
                    1)).encode()
            return json.dumps({"id": 7}).encode()

        env = {"GH_REPO": "o/r", "GITHUB_RUN_ID": "7", "GITHUB_RUN_ATTEMPT": "1", "BASE_REF": ""}
        with mock.patch.object(ci_metrics, "gh", gh), mock.patch.dict(os.environ, env), \
                mock.patch("sys.stderr"):
            m = ci_metrics.collect_this_run()
        self.assertEqual(m["lean"]["plan"]["stale"], 1168)
        self.assertEqual([j["name"] for j in m["lean"]["jobs"]], ["Lean: plan and build"])
        self.assertEqual(len(m["jobs"]), 2)

    def test_local_fallback_assembly_survives_an_unfinished_job(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "assembly.log"
            path.write_text("Built A (2s)\nBuilt A:c.o (300ms)\nBuilt Native:shared (1s)\n")
            env = {"GH_REPO": "o/r", "GITHUB_RUN_ID": "7", "GITHUB_RUN_ATTEMPT": "1",
                   "CI_METRICS_ASSEMBLY_LOG": str(path)}
            def gh(url, *args):
                return b'' if "/jobs?" in url else b'{"id": 7}'
            with mock.patch.object(ci_metrics, "gh", gh), mock.patch.dict(os.environ, env), \
                    mock.patch("sys.stderr"):
                m = ci_metrics.collect_this_run()
            self.assertEqual(m["lean"]["fallback_assembly"],
                             {"built": {"A": 2.0}, "facets": {"A:c.o": 0.3, "Native:shared": 1.0}})
            self.assertIn("Fallback assembly in all-green: 1 modules and 2 native facets",
                          ci_metrics.summary(m))


class RebuildCheck(unittest.TestCase):
    def test_reports_only_observed_unplanned_compilations(self):
        planning = {"status": "available", "plan": {"diagnostics": {"stale_modules": ["A"]}}}
        jobs = [{"job_id": 7, "name": "Lean: shard (1)", "restored_planned": True,
                 "built": {"Check the shard's proofs": {"A": 10, "B": 20},
                           "Restore cache": {"C": 30}}}]
        check = ci_metrics.rebuild_check(jobs, planning)
        self.assertEqual(check, {"status": "available", "jobs": [
            {"job_id": 7, "name": "Lean: shard (1)", "restored_planned": True,
             "unexpected": {"Check the shard's proofs": {"B": 20}}}]})

    def test_missing_or_unverified_snapshots_are_unknown(self):
        for planning in (None, {"status": "unavailable"},
                         {"status": "available", "plan": {}},
                         {"status": "different_attempt", "plan": {
                             "diagnostics": {"stale_modules": []}}}):
            self.assertEqual(ci_metrics.rebuild_check([], planning), {"status": "unavailable"})


class RetainedPlan(unittest.TestCase):
    def fetch(self, plan, attempt="1"):
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as z:
            z.writestr("lean-plan.json", json.dumps(plan))
        def gh(path, *args):
            if "artifacts?" in path:
                return b'{"artifacts": [{"id": 42, "expired": false}]}'
            return data.getvalue()
        with mock.patch.object(ci_metrics, "gh", gh):
            return ci_metrics.fetch_plan("o/r", "7", attempt)

    def test_exact_artifact_is_embedded_in_metrics(self):
        plan = {"targets": [["A"]], "owner": {"A": 0},
                "diagnostics": {"run_id": "7", "run_attempt": "1", "historical_times": {"A": 2.5}}}
        planning = self.fetch(plan)
        self.assertEqual(planning, {"status": "available", "artifact_id": 42, "plan": plan})
        self.assertEqual(ci_metrics.collect({}, [], {}, planning)["lean"]["planning"], planning)

    def test_older_attempt_and_legacy_provenance_are_not_claimed_as_current(self):
        plan = {"diagnostics": {"run_id": "7", "run_attempt": "1"}}
        self.assertEqual(self.fetch(plan, attempt="2")["status"], "different_attempt")
        self.assertEqual(self.fetch({"targets": []})["status"], "unverified")

    def test_missing_and_invalid_artifacts_preserve_collection(self):
        for response in [b'{"artifacts": []}', b'{"artifacts": [{"id": 1, "expired": false}]}']:
            with self.subTest(response=response), mock.patch.object(ci_metrics, "gh", return_value=response), \
                    mock.patch("sys.stderr"):
                self.assertEqual(ci_metrics.fetch_plan("o/r", "7", "1")["status"], "unavailable")


class FetchHistory(unittest.TestCase):
    def test_paginate_past_100_without_repeating_or_exceeding_the_window(self):
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as z:
            z.writestr("ci-metrics.json", '{"version": 2}')
        paths = []
        def gh(path, *args, output=None):
            paths.append(path)
            if "workflows/ci.yml/runs?" in path:
                first = 1 if path.endswith("page=1") else 101
                return json.dumps({"workflow_runs": [{"id": i} for i in range(first, first + 100)]}).encode()
            if "artifacts?" in path:
                return b'{"artifacts": [{"id": 42, "name": "ci-metrics", "expired": false}]}'
            output.write(data.getvalue())
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp)
            for i in range(1, 101):
                (out / f"{i}.json").write_text("existing")
            with mock.patch.object(ci_metrics, "gh", gh), mock.patch("sys.stderr"):
                ci_metrics.fetch(out, 105, "o/r")
            self.assertEqual(len(list(out.glob("[0-9]*.json"))), 105)
            self.assertEqual((out / "1.json").read_text(), "existing")
            self.assertEqual(json.loads((out / "105.json").read_text()), {"version": 2})
        self.assertIn("repos/o/r/actions/workflows/ci.yml/runs?per_page=100&page=2", paths)
        self.assertEqual(sum("artifacts?" in p for p in paths), 5)


if __name__ == "__main__":
    unittest.main()
