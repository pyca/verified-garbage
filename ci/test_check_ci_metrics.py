"""The run's metrics (ci_metrics.py) from its jobs and their logs; no API."""

import unittest

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


if __name__ == "__main__":
    unittest.main()
