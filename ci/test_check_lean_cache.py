"""Exercise the workflow's registry comparison without publishing images."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


WORKFLOW = Path(__file__).resolve().parents[1] / ".github/workflows/ci.yml"


class LeanCachePublishingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        step = WORKFLOW.read_text().split(
            "      - name: Decide whether the cache needs publishing\n", 1
        )[1].split("\n      - ", 1)[0]
        cls.script = textwrap.dedent(step.split("        run: |\n", 1)[1])

    def check_publication(self, labels=None, *, error="", head="current", fail=""):
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
                " print(os.environ['HEAD'])\n"
                "elif sys.argv[1] == 'login':\n"
                " sys.stdin.read()\n"
                " if os.environ['FAIL'] == 'login': sys.exit(1)\n"
                "elif os.environ['ERROR']:\n"
                " print(os.environ['ERROR'], file=sys.stderr)\n"
                " sys.exit(1)\n"
                "else:\n"
                " print(os.environ['LABELS'])\n"
            )
            mock.chmod(0o755)
            for name in ("gh", "docker"):
                (root / name).symlink_to(mock)
            output = root / "output"
            calls = root / "calls"
            output.touch()
            env = dict(
                os.environ,
                PATH=f"{root}:{os.environ['PATH']}",
                RUNNER_TEMP=tmp,
                GITHUB_OUTPUT=str(output),
                GH_REPO="pyca/verified-garbage",
                GITHUB_SHA="current",
                GH_TOKEN="test-token",
                GITHUB_ACTOR="test-actor",
                IMAGE="ghcr.io/pyca/vg-lean-cache:latest",
                CACHE_KEY="checked-cache-zstd5-v1",
                CALLS=str(calls),
                HEAD=head,
                FAIL=fail,
                ERROR=error,
                LABELS=json.dumps(labels),
            )
            result = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", self.script],
                env=env,
                text=True,
                capture_output=True,
            )
            return result, output.read_text(), calls.read_text()

    def test_matching_cache_skips_publication(self):
        result, output, _ = self.check_publication(
            {"io.pyca.lean.cache-key": "checked-cache-zstd5-v1"}
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "")

    def test_changed_or_unlabelled_cache_is_published(self):
        for labels in ({"io.pyca.lean.cache-key": "older-cache"}, {}, None):
            with self.subTest(labels=labels):
                result, output, _ = self.check_publication(labels)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "needed=true\n")

    def test_first_publication(self):
        for error in ("manifest unknown", "404 Not Found"):
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

    def test_superseded_commit_skips_registry_access(self):
        result, output, calls = self.check_publication(head="newer")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "")
        self.assertNotIn("docker", calls)

    def test_api_or_login_failure_stops_publication(self):
        for fail in ("api", "login"):
            with self.subTest(fail=fail):
                result, output, _ = self.check_publication(fail=fail)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(output, "")


if __name__ == "__main__":
    unittest.main()
