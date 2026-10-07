"""The run's metrics (ci_metrics.py) from what the Lean jobs record; no API."""

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

import ci_metrics

SCRIPT = pathlib.Path(__file__).with_name("ci_metrics.py")
LOG = """\
✔ [10/20] Built VerifiedGarbage.A (1.5s)
✔ [11/20] Built VerifiedGarbage.B (250ms)
✔ [12/20] Built VerifiedGarbage.A:c.o (3s)
"""


def run(*args, stdin=""):
    return subprocess.run([sys.executable, SCRIPT, *args], input=stdin, capture_output=True, text=True, check=True).stdout


def api_job(name, start, end, steps=()):
    return {"name": name, "conclusion": "success", "runner_name": "r", "labels": ["ubuntu-latest"],
            "created_at": "2026-10-07T12:00:00Z", "started_at": start, "completed_at": end,
            "steps": [{"name": n, "conclusion": "success", "started_at": a, "completed_at": b} for n, a, b in steps]}


class Records(unittest.TestCase):
    def test_shard(self):
        r = json.loads(run("shard", "2", "planned", "exact", "planned", stdin=LOG))
        # A facet's line (`A:c.o`) is not a module's.
        self.assertEqual(r["times"], {"VerifiedGarbage.A": 1.5, "VerifiedGarbage.B": 0.25})
        self.assertEqual((r["kind"], r["shard"], r["restored"]), ("shard", "2", "planned"))

    def test_assembly(self):
        r = json.loads(run("assembly", "1", "", stdin=""))
        self.assertEqual((r["kind"], r["id"], r["restored"], r["times"]), ("assembly", "1", "", {}))


class Collect(unittest.TestCase):
    plan = {"stale": 3, "work": 40, "loads": [10, 8], "targets": [["X"], ["Y"]]}
    jobs = [
        api_job("Lean: shard (1)", "2026-10-07T12:01:00Z", "2026-10-07T12:05:00Z",
                [("Check the shard's proofs (and the axiom audit)", "2026-10-07T12:02:00Z", "2026-10-07T12:04:00Z")]),
        api_job("Lean: shard (2)", "2026-10-07T12:01:30Z", "2026-10-07T12:03:00Z",
                [("Check the shard's proofs (and the axiom audit)", "2026-10-07T12:02:00Z", "2026-10-07T12:02:30Z")]),
        api_job("Coverage", "2026-10-07T12:00:10Z", None),
    ]
    records = [
        {"kind": "shard", "shard": "2", "planned": "k", "exact": "e", "restored": "",
         "times": {"A": 2.0, "C": 5.0}},
        {"kind": "shard", "shard": "1", "planned": "k", "exact": "e", "restored": "k",
         "times": {"A": 3.0, "B": 4.0}},
        {"kind": "assembly", "id": "1", "restored": "k", "times": {"D": 1.0}},
    ]

    def metrics(self):
        return ci_metrics.collect({"id": 7, "event": "pull_request", "base_ref": "main"}, self.jobs, self.plan,
                                  self.records)

    def test_shards(self):
        m = self.metrics()
        one, two = m["lean"]["shards"]
        self.assertEqual((one["shard"], one["estimate_s"], one["build_s"], one["modules"], one["work"]),
                         (1, 10, 120, 2, 7.0))
        self.assertTrue(one["restored_planned"])
        # Shard 2's restore failed: it restored nothing.
        self.assertEqual((two["estimate_s"], two["build_s"], two["restored_planned"]), (8, 30, False))
        # A was built twice: the cheaper build counts as duplicate work.
        self.assertEqual(m["lean"]["duplicate_work"], 2.0)
        self.assertEqual(m["lean"]["plan"], {"stale": 3, "work": 40, "count": 2, "estimates": [10, 8]})
        self.assertEqual(m["lean"]["assemblies"][0]["modules"], 1)

    def test_jobs(self):
        m = self.metrics()
        self.assertEqual(m["run"]["base_ref"], "main")
        shard = m["jobs"][0]
        self.assertEqual((shard["queued_s"], shard["duration_s"]), (60, 240))
        # A job still running has no duration.
        self.assertIsNone(m["jobs"][2]["duration_s"])

    def test_without_a_lean_build(self):
        m = ci_metrics.collect({"id": 7}, [], None, [])
        self.assertIsNone(m["lean"]["plan"])
        self.assertIn("No plan", ci_metrics.summary(m))

    def test_end_to_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            (d / "records").mkdir()
            for r in self.records:
                name = f"lean-{r['kind']}-{r.get('shard', r.get('id'))}.json"
                (d / "records" / name).write_text(json.dumps(r))
            (d / "run.json").write_text(json.dumps({"id": 7}))
            (d / "jobs.json").write_text(json.dumps(self.jobs))
            (d / "plan.json").write_text(json.dumps(self.plan))
            out = run("collect", d / "run.json", d / "jobs.json", d / "plan.json", d / "records")
            (d / "m.json").write_text(out)
            text = run("summary", d / "m.json")
        self.assertIn("| 2 | 8 s | 30 s | 2 | 7 s | **no** (none) |", text)
        self.assertIn("Assembly (1): built 1 modules", text)
        self.assertIn("| Lean: shard (1) | 60 s | 240 s |", text)


if __name__ == "__main__":
    unittest.main()
