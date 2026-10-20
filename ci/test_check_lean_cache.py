"""Exercise the workflow's registry comparison without publishing images."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


WORKFLOW = Path(__file__).resolve().parents[1] / ".github/workflows/lean-cache.yml"


class CheckedBuildTests(unittest.TestCase):
    def check_build(self, hit, dependency_key=None):
        step = WORKFLOW.read_text().split("      - name: Check the checked build was restored\n", 1)[1]
        script = textwrap.dedent(step.split("        run: |\n", 1)[1].split("\n      - ", 1)[0])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            if dependency_key is not None:
                path = root / "lean/.lake/ltar/mathlib-cache-key"
                path.parent.mkdir(parents=True)
                path.write_text(dependency_key + "\n")
            output = root / "output"
            output.touch()
            result = subprocess.run(["bash", "-e", "-c", script], cwd=root,
                                    env=dict(os.environ, CACHE_HIT=hit, GITHUB_OUTPUT=str(output)),
                                    capture_output=True, text=True)
            return result, output.read_text()

    def test_exact_hit_passes_the_saved_dependency_key(self):
        result, output = self.check_build("true", "exact-mathlib-key")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "key=exact-mathlib-key\n")

    def test_old_cache_can_use_normal_preparation(self):
        result, output = self.check_build("true")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "")

    def test_miss_or_fallback_stops_before_dependency_setup(self):
        for hit in ("false", ""):
            with self.subTest(hit=hit):
                result, output = self.check_build(hit, "stale-key")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("The checked build cache is missing", result.stdout)
                self.assertEqual(output, "")


class LeanCachePublishingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        step = WORKFLOW.read_text().split(
            "      - name: Decide whether the cache needs publishing\n", 1
        )[1].split("\n      - ", 1)[0]
        cls.script = textwrap.dedent(step.split("        run: |\n", 1)[1])

    def check_publication(self, annotations=None, *, error="", status="ahead", fail=""):
        manifest = {"schemaVersion": 2}
        if annotations is not None:
            manifest["annotations"] = annotations
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mock = root / "mock"
            mock.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, pathlib, sys\n"
                "with open(os.environ['CALLS'], 'a') as f:\n"
                " f.write(pathlib.Path(sys.argv[0]).name + ' ' + ' '.join(sys.argv[1:]) + '\\n')\n"
                "if pathlib.Path(sys.argv[0]).name == 'gh':\n"
                " if os.environ['FAIL'] == 'api': sys.exit(1)\n"
                " print(os.environ['STATUS'])\n"
                "else:\n"
                " with open(os.environ['STDIN'], 'a') as f: f.write(sys.stdin.read())\n"
                " if os.environ['ERROR']:\n"
                "  print(os.environ['ERROR'], file=sys.stderr)\n"
                "  sys.exit(1)\n"
                " print(json.dumps(json.loads(os.environ['MANIFEST'])))\n"
            )
            mock.chmod(0o755)
            for name in ("gh", "oras"):
                (root / name).symlink_to(mock)
            output = root / "output"
            calls = root / "calls"
            stdin = root / "stdin"
            output.touch()
            stdin.touch()
            env = dict(
                os.environ,
                PATH=f"{root}:{os.environ['PATH']}",
                RUNNER_TEMP=tmp,
                GITHUB_OUTPUT=str(output),
                GH_REPO="pyca/verified-garbage",
                HEAD_SHA="current",
                GH_TOKEN="test-token",
                GITHUB_ACTOR="test-actor",
                IMAGE="ghcr.io/pyca/vg-lean-cache:latest",
                CACHE_KEY="checked-cache-zstd5-oras-v3",
                CALLS=str(calls),
                STDIN=str(stdin),
                STATUS=status,
                FAIL=fail,
                ERROR=error,
                MANIFEST=json.dumps(manifest),
            )
            result = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", self.script],
                env=env,
                text=True,
                capture_output=True,
            )
            calls = calls.read_text()
            # The token goes to oras on stdin, never in its arguments.
            self.assertNotIn("test-token", calls)
            if "oras" in calls:
                self.assertIn("oras manifest fetch --username test-actor --password-stdin", calls)
                self.assertEqual(stdin.read_text(), "test-token")
            return result, output.read_text(), calls

    def test_matching_cache_skips_publication(self):
        result, output, calls = self.check_publication(
            {"io.pyca.lean.cache-key": "checked-cache-zstd5-oras-v3", "org.opencontainers.image.revision": "older"}
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "")
        self.assertNotIn("gh ", calls)

    def test_changed_or_unannotated_cache_is_published(self):
        for annotations in ({"io.pyca.lean.cache-key": "older-cache"}, {}, None):
            with self.subTest(annotations=annotations):
                result, output, calls = self.check_publication(annotations)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "needed=true\n")
                # Without a published revision there is nothing to compare.
                self.assertNotIn("gh ", calls)

    def test_older_commits_cache_is_replaced(self):
        # Main may have moved past this commit too: an older cache is still
        # replaced, so a stream of merges cannot keep the cache from updating.
        for status in ("ahead", "identical", "diverged"):
            with self.subTest(status=status):
                result, output, calls = self.check_publication(
                    {"io.pyca.lean.cache-key": "older-cache", "org.opencontainers.image.revision": "older"},
                    status=status,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "needed=true\n")
                self.assertIn("gh api repos/pyca/verified-garbage/compare/older...current --jq .status", calls)

    def test_newer_commits_cache_is_kept(self):
        result, output, _ = self.check_publication(
            {"io.pyca.lean.cache-key": "newer-cache", "org.opencontainers.image.revision": "newer"},
            status="behind",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "")

    def test_first_publication(self):
        for error in (
            "manifest unknown",
            'Error response from registry: failed to fetch the content of "ghcr.io/pyca/vg-lean-cache:latest": '
            "ghcr.io/pyca/vg-lean-cache:latest: not found",
        ):
            with self.subTest(error=error):
                result, output, _ = self.check_publication(error=error)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "needed=true\n")

    def test_registry_errors_do_not_trigger_publication(self):
        for error in ("401 Unauthorized", "403 Forbidden", "429 Too Many Requests", "503 unavailable"):
            with self.subTest(error=error):
                result, output, _ = self.check_publication(error=error)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(output, "")

    def test_api_failure_stops_publication(self):
        result, output, _ = self.check_publication(
            {"io.pyca.lean.cache-key": "older-cache", "org.opencontainers.image.revision": "older"}, fail="api"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, "")

if __name__ == "__main__":
    unittest.main()
