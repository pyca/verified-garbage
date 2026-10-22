"""Resumable metrics collection and export, with no GitHub calls in tests."""

import contextlib
import datetime as dt
import gzip
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock
import zipfile

import ci_metrics as metrics


class Fetch(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.out = self.root / "metrics"
        self.enterContext(contextlib.redirect_stderr(io.StringIO()))
        self.end = dt.datetime(2026, 10, 21, 20, tzinfo=dt.timezone.utc)
        self.runs = [{"id": n, "status": "completed", "conclusion": "success", "run_attempt": 2}
                     for n in range(1, 7)]

    def archive(self, run_id):
        document = {"run": {"id": run_id, "attempt": 1},
                    "lean": {"planning": {"plan": {"diagnostics": {"kept": True}}}}}
        raw = (json.dumps(document, indent=2) + "\n").encode()
        packed = io.BytesIO()
        with zipfile.ZipFile(packed, "w") as archive:
            archive.writestr("ci-metrics.json", raw)
        return raw, packed.getvalue()

    def api(self, path, *args, output=None):
        if "/workflows/" in path:
            return json.dumps({"total_count": len(self.runs), "workflow_runs": self.runs}).encode()
        if "/runs/" in path:
            run_id = int(path.split("/runs/")[1].split("/")[0])
            if run_id == 2:
                arts = []
            else:
                arts = [{"id": run_id * 10, "name": "ci-metrics", "expired": run_id == 3,
                         "created_at": "2026-10-21T12:00:00Z"}]
            return json.dumps({"artifacts": arts}).encode()
        run_id = int(path.split("/artifacts/")[1].split("/")[0]) // 10
        if run_id == 4:
            raise subprocess.CalledProcessError(1, ["gh"], stderr=b'Get "https://storage/file?sig=secret": Forbidden')
        output.write(b"not a ZIP" if run_id == 5 else self.archive(run_id)[1])

    def collection(self):
        return json.loads((self.out / "collection.json").read_text())

    def test_time_window_preserves_metrics_and_records_partial_coverage(self):
        with mock.patch.object(metrics, "gh", side_effect=self.api) as api:
            self.assertEqual(metrics.fetch(self.out, hours=8, end=self.end), 1)
        first_path = api.call_args_list[0].args[0]
        self.assertIn("created=2026-10-21T12%3A00%3A00Z..2026-10-21T20%3A00%3A00Z", first_path)
        result = self.collection()
        self.assertTrue(result["selection_complete"])
        self.assertEqual(result["inspected_runs"], 6)
        self.assertEqual([r["run"]["id"] for r in result["runs"]], [1, 6])
        self.assertEqual([r["run"]["id"] for r in result["missing"]], [2, 3])
        self.assertEqual([r["run"]["id"] for r in result["errors"]], [4, 5])
        self.assertEqual([r["artifact_id"] for r in result["errors"]], [40, 50])
        self.assertNotIn("secret", json.dumps(result))
        self.assertIn("?[redacted]", result["errors"][0]["error"])
        self.assertEqual((self.out / "1.json").read_bytes(), self.archive(1)[0])
        row = result["runs"][0]
        self.assertEqual(row["artifact_id"], 10)
        self.assertEqual(row["artifact"]["created_at"], "2026-10-21T12:00:00Z")
        self.assertEqual(row["metrics_run"]["attempt"], 1)
        self.assertEqual(row["downloaded_run"]["run_attempt"], 2)
        self.assertFalse((self.out / "4.json").exists())
        self.assertFalse((self.out / "5.json").exists())

    def test_cached_provenance_survives_other_windows_and_later_reruns(self):
        self.runs = self.runs[:1]
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            self.assertEqual(metrics.fetch(self.out, 1), 0)
        self.runs = [{"id": 6}]
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            self.assertEqual(metrics.fetch(self.out, hours=8, end=self.end), 0)
        self.runs = [{"id": 1, "run_attempt": 3}]
        with mock.patch.object(metrics, "gh", side_effect=self.api) as api:
            self.assertEqual(metrics.fetch(self.out, 1), 0)
            self.assertEqual(api.call_count, 1)  # Only enumerate; no artifact request.
        row = self.collection()["runs"][0]
        self.assertTrue(row["cached"])
        self.assertEqual(row["run"]["run_attempt"], 3)
        self.assertEqual(row["downloaded_run"]["run_attempt"], 2)
        self.assertEqual(row["metrics_run"]["attempt"], 1)
        self.assertEqual(row["artifact_id"], 10)

    def test_legacy_files_are_preserved_with_unknown_artifact_provenance(self):
        self.out.mkdir()
        data = self.archive(1)[0]
        (self.out / "1.json").write_bytes(data)
        self.runs = self.runs[:1]
        with mock.patch.object(metrics, "gh", side_effect=self.api) as api:
            self.assertEqual(metrics.fetch(self.out, 1), 0)
            self.assertEqual(api.call_count, 1)
        row = self.collection()["runs"][0]
        self.assertEqual(row["provenance"], "legacy_local")
        self.assertIsNone(row["artifact_id"])
        self.assertNotIn("downloaded_run", row)
        self.assertEqual((self.out / "1.json").read_bytes(), data)

    def test_artifacts_paginate_and_choose_latest_retained_metrics(self):
        self.runs = self.runs[:1]

        def api(path, *args, output=None):
            if "/runs/1/artifacts?" in path:
                rows = ([{"id": n, "name": "other", "expired": False} for n in range(100)]
                        if path.endswith("page=1") else [
                            {"id": 999, "name": "ci-metrics", "expired": True},
                            {"id": 10, "name": "ci-metrics", "expired": False},
                            {"id": 9, "name": "ci-metrics", "expired": False}])
                return json.dumps({"artifacts": rows}).encode()
            return self.api(path, *args, output=output)

        with mock.patch.object(metrics, "gh", side_effect=api) as gh:
            self.assertEqual(metrics.fetch(self.out, 1), 0)
        self.assertEqual(self.collection()["runs"][0]["artifact_id"], 10)
        self.assertTrue(any("artifacts?name=ci-metrics&per_page=100&page=2" in c.args[0]
                            for c in gh.call_args_list))

    def test_filtered_search_cap_is_recorded_instead_of_silent_truncation(self):
        response = json.dumps({"total_count": 1001, "workflow_runs": self.runs}).encode()
        with mock.patch.object(metrics, "gh", return_value=response):
            self.assertEqual(metrics.fetch(self.out, hours=8, end=self.end), 1)
        result = self.collection()
        self.assertFalse(result["selection_complete"])
        self.assertEqual(result["runs"], [])
        self.assertIn("1000", result["errors"][0]["error"])

    def test_search_failure_keeps_successful_files_and_a_readable_manifest(self):
        self.runs = [{"id": n} for n in range(1, 101)]
        self.out.mkdir()
        for run in self.runs:
            (self.out / f"{run['id']}.json").write_text("{}")

        def api(path, *args, **kwargs):
            if path.endswith("page=2"):
                raise OSError("connection lost")
            return self.api(path, *args, **kwargs)

        with mock.patch.object(metrics, "gh", side_effect=api):
            self.assertEqual(metrics.fetch(self.out, 101), 1)
        result = self.collection()
        self.assertFalse(result["selection_complete"])
        self.assertEqual(len(result["runs"]), 100)
        self.assertEqual(len(list(self.out.glob("[0-9]*.json"))), 100)

    def test_empty_window_is_complete_and_not_a_download_failure(self):
        self.runs = []
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            self.assertEqual(metrics.fetch(self.out, hours=8, end=self.end), 0)
        self.assertTrue(self.collection()["selection_complete"])
        self.assertEqual(self.collection()["inspected_runs"], 0)

    def test_collection_directory_cannot_silently_change_repository(self):
        self.runs = []
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            metrics.fetch(self.out, 1)
        previous = (self.out / "collection.json").read_bytes()
        with mock.patch.object(metrics, "gh", side_effect=AssertionError("no network")):
            with self.assertRaisesRegex(ValueError, "different repository"):
                metrics.fetch(self.out, 1, "another/repository")
        self.assertEqual((self.out / "collection.json").read_bytes(), previous)

    def test_invalid_count_window_combinations_fail_without_network_calls(self):
        with mock.patch.object(metrics, "gh", side_effect=AssertionError("no network")):
            for args in ([str(self.out), "10", "--hours", "8"],
                         [str(self.out), "--end", "2026-10-21T20:00:00Z"],
                         [str(self.out), "--hours", "0"],
                         [str(self.out), "--start", "2026-10-21T20:00:00"],
                         [str(self.out), "0"]):
                with self.subTest(args=args), self.assertRaises(SystemExit) as error:
                    metrics.main(["fetch", *args])
                self.assertNotEqual(error.exception.code, 0)

    def test_bundle_exports_only_last_selection_and_preserves_provenance(self):
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            metrics.fetch(self.out, 6)
        (self.out / "999.json").write_text('{"unrelated":true}')
        self.runs = self.runs[:1]
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            metrics.fetch(self.out, 1)
        output = self.root / "bundle.json.gz"
        with mock.patch.object(metrics, "gh", side_effect=AssertionError("export is offline")):
            self.assertEqual(metrics.main(["bundle", str(self.out), "--output", str(output)]), 0)
        with gzip.open(output, "rt") as stream:
            bundle = json.load(stream)
        self.assertNotIn("cached_runs", bundle)
        self.assertEqual(len(bundle["runs"]), 1)
        row = bundle["runs"][0]
        self.assertEqual(row["files"]["ci-metrics.json"], json.loads(self.archive(1)[0]))
        self.assertEqual(row["artifact_id"], 10)
        self.assertEqual(row["run"]["run_attempt"], 2)
        self.assertEqual(row["metrics_run"]["attempt"], 1)

    def test_bundle_preserves_partial_coverage_and_refuses_overwrites(self):
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            metrics.fetch(self.out, 6)
        output = self.root / "partial.json.gz"
        metrics.bundle(self.out, output)
        original = output.read_bytes()
        with gzip.open(output, "rt") as stream:
            exported = json.load(stream)
        self.assertEqual(exported["errors"], self.collection()["errors"])
        self.assertEqual(exported["missing"], self.collection()["missing"])
        with self.assertRaises(FileExistsError):
            metrics.bundle(self.out, output)
        self.assertEqual(output.read_bytes(), original)

    def test_bad_local_metrics_leave_no_incomplete_bundle(self):
        self.runs = self.runs[:1]
        with mock.patch.object(metrics, "gh", side_effect=self.api):
            metrics.fetch(self.out, 1)
        (self.out / "1.json").write_text('{"truncated":')
        output = self.root / "broken.json.gz"
        with self.assertRaises(ValueError):
            metrics.bundle(self.out, output)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
