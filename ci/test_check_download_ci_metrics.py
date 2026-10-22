"""Metrics transport preserves data and makes incomplete samples explicit."""

import argparse
import contextlib
import datetime as dt
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import zipfile

import download_ci_metrics as download


class Transport(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.enterContext(contextlib.redirect_stderr(io.StringIO()))

    def source(self):
        path = self.root / "metrics.json.gz"
        path.write_bytes(gzip.compress(b'{"runs":[],"missing":[],"errors":[]}\n'))
        return path

    def test_split_join_preserves_compressed_bytes_with_a_short_final_part(self):
        source = self.source()
        directory = self.root / "upload"
        download.split(source, directory, 7)
        manifest = json.loads((directory / "manifest.json").read_text())
        self.assertEqual(manifest["size"], source.stat().st_size)
        self.assertEqual(manifest["sha256"], hashlib.sha256(source.read_bytes()).hexdigest())
        self.assertGreater(len(manifest["parts"]), 1)
        self.assertTrue(all(0 < p["size"] <= 7 for p in manifest["parts"]))
        output = self.root / "restored.json.gz"
        download.join(directory / "manifest.json", output)
        self.assertEqual(source.read_bytes(), output.read_bytes())
        self.assertEqual(json.loads(gzip.decompress(output.read_bytes()))["runs"], [])

    def test_split_refuses_mixing_with_an_existing_upload(self):
        source = self.source()
        directory = self.root / "upload"
        download.split(source, directory, source.stat().st_size)
        with self.assertRaises(FileExistsError):
            download.split(source, directory, 7)
        self.assertEqual(len(json.loads((directory / "manifest.json").read_text())["parts"]), 1)

    def test_invalid_parts_never_leave_a_partial_output(self):
        for problem in ("missing", "corrupt", "reordered", "total_checksum", "path", "drive_path"):
            with self.subTest(problem=problem):
                directory = self.root / problem
                download.split(self.source(), directory, 7)
                path = directory / "manifest.json"
                manifest = json.loads(path.read_text())
                first = directory / manifest["parts"][0]["name"]
                if problem == "missing":
                    first.unlink()
                elif problem == "corrupt":
                    first.write_bytes(b"x" * first.stat().st_size)
                elif problem == "reordered":
                    manifest["parts"].reverse()
                elif problem == "total_checksum":
                    manifest["sha256"] = "0" * 64
                elif problem == "drive_path":
                    manifest["file"] = "C:outside"
                else:
                    manifest["parts"][0]["name"] = "../outside"
                path.write_text(json.dumps(manifest))
                output = self.root / "restored.gz"
                with self.assertRaises((OSError, ValueError)):
                    download.join(path, output)
                self.assertFalse(output.exists())

    def test_join_preserves_existing_output(self):
        directory = self.root / "upload"
        download.split(self.source(), directory, 7)
        output = self.root / "keep.gz"
        output.write_bytes(b"existing data")
        with self.assertRaises(FileExistsError):
            download.join(directory / "manifest.json", output)
        self.assertEqual(output.read_bytes(), b"existing data")


class Collection(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.enterContext(contextlib.redirect_stderr(io.StringIO()))
        self.args = argparse.Namespace(repository="pyca/verified-garbage", workflow="ci.yml",
                                       start=None, end=dt.datetime(2026, 10, 21, 20, tzinfo=dt.timezone.utc),
                                       hours=8, output=self.root / "nested/metrics.json.gz")

    def test_pages_do_not_truncate_after_100_runs_or_artifacts(self):
        for key in ("workflow_runs", "artifacts"):
            with self.subTest(key=key):
                def api(endpoint):
                    rows = list(range(100)) if endpoint.endswith("&page=1") else [100]
                    return json.dumps({"total_count": 101, key: rows})
                with mock.patch.object(download, "api", side_effect=api):
                    self.assertEqual(list(download.pages("endpoint?name=ci-metrics", key)), list(range(101)))

    def test_large_filtered_search_is_explicitly_rejected(self):
        with mock.patch.object(download, "api", return_value=json.dumps({"total_count": 1001})):
            with self.assertRaisesRegex(RuntimeError, "smaller time window"):
                list(download.pages("endpoint", "workflow_runs"))

    def test_fetch_keeps_metrics_and_records_partial_coverage(self):
        runs = [{"id": n, "status": "completed", "conclusion": "success", "run_attempt": 2}
                for n in range(1, 6)]
        runs[-1]["status"] = "in_progress"

        def pages(endpoint, key):
            if key == "workflow_runs":
                self.assertIn("created=2026-10-21T12%3A00%3A00Z..2026-10-21T20%3A00%3A00Z", endpoint)
                return runs
            if "/runs/1/" in endpoint:
                return [{"id": 10, "name": "ci-metrics", "expired": False},
                        {"id": 11, "name": "different-artifact", "expired": False}]
            if "/runs/2/" in endpoint:
                return [{"id": 20, "name": "ci-metrics", "expired": True}]
            if "/runs/3/" in endpoint:
                raise RuntimeError("API unavailable")
            if "/runs/4/" in endpoint:
                return [{"id": 40, "name": "ci-metrics", "expired": False}]
            return []

        documents = {"ci-metrics.json": {"run": {"id": 1, "attempt": 1},
                                          "lean": {"planning": {"plan": {"diagnostics": {"kept": True}}}}}}

        def artifact(base, artifact_id):
            if artifact_id == 40:
                raise zipfile.BadZipFile("broken artifact")
            return documents

        with mock.patch.object(download, "pages", side_effect=pages), \
                mock.patch.object(download, "artifact_documents", side_effect=artifact):
            self.assertEqual(download.fetch(self.args), 1)
        with gzip.open(self.args.output, "rt") as stream:
            bundle = json.load(stream)
        self.assertEqual(bundle["runs"][0]["files"], documents)
        self.assertEqual(bundle["runs"][0]["run"]["run_attempt"], 2)
        self.assertEqual(bundle["inspected_runs"], 5)
        self.assertEqual([r["run"]["id"] for r in bundle["errors"]], [2, 3, 4])
        self.assertEqual([r["run"]["id"] for r in bundle["missing"]], [5])

    def test_empty_window_is_a_valid_bundle(self):
        with mock.patch.object(download, "pages", return_value=[]):
            self.assertEqual(download.fetch(self.args), 0)
        with gzip.open(self.args.output, "rt") as stream:
            self.assertEqual(json.load(stream)["inspected_runs"], 0)

    def test_fatal_search_error_removes_incomplete_output(self):
        with mock.patch.object(download, "pages", side_effect=RuntimeError("search failed")):
            with self.assertRaisesRegex(RuntimeError, "search failed"):
                download.fetch(self.args)
        self.assertFalse(self.args.output.exists())

    def test_existing_bundle_is_preserved_without_network_access(self):
        self.args.output.parent.mkdir()
        self.args.output.write_bytes(b"keep")
        with mock.patch.object(download, "pages", side_effect=AssertionError("no network")):
            with self.assertRaises(FileExistsError):
                download.fetch(self.args)
        self.assertEqual(self.args.output.read_bytes(), b"keep")

    def test_archive_documents_are_read_without_extracting_paths(self):
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as archive:
            archive.writestr("nested/ci-metrics.json", '{"lean":{"planning":{"kept":true}}}')
            archive.writestr("../other.json", '{"value":2}')
            archive.writestr("ignored.txt", "not JSON")

        def api(endpoint, output):
            output.write(data.getvalue())

        with mock.patch.object(download, "api", side_effect=api):
            documents = download.artifact_documents("base", 1)
        self.assertTrue(documents["nested/ci-metrics.json"]["lean"]["planning"]["kept"])
        self.assertEqual(documents["../other.json"], {"value": 2})

    def test_signed_storage_urls_are_redacted_from_download_errors(self):
        failure = mock.Mock(returncode=1, stderr=b'Get "https://storage.invalid/file.zip?sig=secret&se=expiry": Forbidden')
        with mock.patch.object(download.subprocess, "run", return_value=failure):
            with self.assertRaisesRegex(RuntimeError, r"file.zip\?\[redacted\]") as error:
                download.api("artifact/zip")
        self.assertNotIn("secret", str(error.exception))


@unittest.skipUnless(importlib.util.find_spec("ijson"), "run with uv run --with ijson for streaming tests")
class Streaming(unittest.TestCase):
    def test_summary_preserves_coverage_and_provenance_without_full_bundle_load(self):
        metrics = {"run": {"attempt": 1}, "collection": {"jobs_complete": False},
                   "jobs": [{"name": "Lean: shard (1)", "duration_s": 10}],
                   "lean": {"planning": {"status": "different_attempt", "plan": {"graph": "omitted"}},
                            "missing_logs": ["failed job"],
                            "jobs": [{"built": {"proofs": {"A": 3}}}, {"built": {"proofs": {"A": 4}}}]}}
        bundle = {"repository": "pyca/verified-garbage", "runs": [
            {"run": {"id": 1, "status": "completed", "conclusion": "success", "run_attempt": 2},
             "artifact_id": 9, "files": {"ci-metrics.json": metrics}}],
            "missing": [{"run": {"id": 2}}], "errors": [{"error": "failed download"}]}
        with tempfile.TemporaryDirectory() as temp:
            for compressed in (False, True):
                path = Path(temp) / ("bundle.json.gz" if compressed else "bundle.json")
                data = json.dumps(bundle).encode()
                path.write_bytes(gzip.compress(data) if compressed else data)
                with mock.patch.object(json, "load", side_effect=AssertionError("no full bundle load")):
                    result = download.summary(path)
                self.assertEqual(result["missing"], bundle["missing"])
                self.assertEqual(result["errors"], bundle["errors"])
                self.assertEqual(result["unique_runs_with_artifacts"], 1)
                row = result["runs"][0]
                self.assertEqual(row["metrics_run"], {"attempt": 1})
                self.assertEqual(row["run"]["run_attempt"], 2)
                self.assertEqual(row["planning_status"], "different_attempt")
                self.assertEqual(row["module_build_observations"], 2)
                self.assertEqual(row["summed_module_seconds"], 7)
                self.assertNotIn("graph", json.dumps(result))

    def test_reader_rejects_truncated_or_non_bundle_inputs(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "bad.json.gz"
            for text in ('{"runs":[{"run":', '[]', '{"jobs":[]}'):
                path.write_bytes(gzip.compress(text.encode()))
                with self.assertRaises(ValueError):
                    list(download.records(path))


if __name__ == "__main__":
    unittest.main()
