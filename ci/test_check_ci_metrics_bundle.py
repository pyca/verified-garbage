"""Metrics transport preserves data and makes incomplete samples explicit."""

import contextlib
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import ci_metrics_bundle as transport


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
        transport.split(source, directory, 7)
        manifest = json.loads((directory / "manifest.json").read_text())
        self.assertEqual(manifest["size"], source.stat().st_size)
        self.assertEqual(manifest["sha256"], hashlib.sha256(source.read_bytes()).hexdigest())
        self.assertGreater(len(manifest["parts"]), 1)
        self.assertTrue(all(0 < p["size"] <= 7 for p in manifest["parts"]))
        output = self.root / "restored.json.gz"
        transport.join(directory / "manifest.json", output)
        self.assertEqual(source.read_bytes(), output.read_bytes())
        self.assertEqual(json.loads(gzip.decompress(output.read_bytes()))["runs"], [])

    def test_split_refuses_mixing_with_an_existing_upload(self):
        source = self.source()
        directory = self.root / "upload"
        transport.split(source, directory, source.stat().st_size)
        with self.assertRaises(FileExistsError):
            transport.split(source, directory, 7)
        self.assertEqual(len(json.loads((directory / "manifest.json").read_text())["parts"]), 1)

    def test_invalid_parts_never_leave_a_partial_output(self):
        for problem in ("missing", "corrupt", "reordered", "total_checksum", "path", "drive_path"):
            with self.subTest(problem=problem):
                directory = self.root / problem
                transport.split(self.source(), directory, 7)
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
                    transport.join(path, output)
                self.assertFalse(output.exists())

    def test_join_preserves_existing_output(self):
        directory = self.root / "upload"
        transport.split(self.source(), directory, 7)
        output = self.root / "keep.gz"
        output.write_bytes(b"existing data")
        with self.assertRaises(FileExistsError):
            transport.join(directory / "manifest.json", output)
        self.assertEqual(output.read_bytes(), b"existing data")


@unittest.skipUnless(importlib.util.find_spec("ijson"), "run with uv run --with ijson for streaming tests")
class Streaming(unittest.TestCase):
    def test_summary_preserves_coverage_and_provenance_without_full_bundle_load(self):
        metrics = {"run": {"attempt": 1}, "collection": {"jobs_complete": False},
                   "jobs": [{"name": "Lean: shard (1)", "duration_s": 10}],
                   "lean": {"planning": {"status": "different_attempt", "plan": {"graph": "omitted"}},
                            "missing_logs": ["failed job"],
                            "jobs": [{"built": {"proofs": {"A": 3}}}, {"built": {"proofs": {"A": 4}}}]}}
        bundle = {"repository": "pyca/verified-garbage", "selection_complete": False, "inspected_runs": 3, "runs": [
            {"run": {"id": 1, "status": "completed", "conclusion": "success", "run_attempt": 2},
             "artifact_id": 9, "files": {"ci-metrics.json": metrics}}],
            "missing": [{"run": {"id": 2}}], "errors": [{"error": "failed download"}]}
        with tempfile.TemporaryDirectory() as temp:
            for compressed in (False, True):
                path = Path(temp) / ("bundle.json.gz" if compressed else "bundle.json")
                data = json.dumps(bundle).encode()
                path.write_bytes(gzip.compress(data) if compressed else data)
                with mock.patch.object(json, "load", side_effect=AssertionError("no full bundle load")):
                    result = transport.summary(path)
                self.assertEqual(result["missing"], bundle["missing"])
                self.assertEqual(result["errors"], bundle["errors"])
                self.assertEqual(result["unique_runs_with_artifacts"], 1)
                self.assertFalse(result["selection_complete"])
                self.assertEqual(result["inspected_runs"], 3)
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
                    list(transport.records(path))


if __name__ == "__main__":
    unittest.main()
