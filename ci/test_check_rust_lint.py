"""The targets `rust-lint` lints each crate for (ci/rust_lint.py), and that
the lint image has each one's standard library."""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib
import unittest
from unittest import mock

import rust_lint

CI = Path(__file__).resolve().parent
LINT = tomllib.loads((CI / "rust_matrix.toml").read_text())["lint"]


def run(*args):
    env = dict(os.environ, LINT=json.dumps(LINT))
    return subprocess.run([sys.executable, str(CI / "rust_lint.py"), *args], env=env,
                          capture_output=True, text=True, check=True).stdout.strip()


class Targets(unittest.TestCase):
    def test_the_library_lints_every_target(self):
        self.assertEqual(run("targets", "library").split(","), [e["target"] for e in LINT])

    def test_the_benchmarks_lint_the_linux_targets(self):
        targets = run("targets", "benchmarks").split(",")
        self.assertEqual(targets, [e["target"] for e in LINT if e.get("bench")])
        self.assertTrue(all("-linux-" in t for t in targets))
        self.assertNotIn("thumbv7neon-unknown-linux-gnueabihf", targets)

    def test_benchmarks_lint_one_target_at_a_time(self):
        calls = []
        with mock.patch.dict(os.environ, LINT=json.dumps(LINT)), \
                mock.patch.object(rust_lint, "cargo", lambda args, cwd: calls.append((args, cwd))):
            rust_lint.run("benchmarks")
        (fmt, _), *clippy = calls
        self.assertEqual(fmt, ["fmt", "--check"])
        # One target at a time (see ci/rust_lint.py).
        self.assertEqual([args[args.index("--target") + 1] for args, _ in clippy],
                         [e["target"] for e in LINT if e.get("bench")])
        self.assertTrue(all(args.count("--target") == 1 and cwd == CI.parent / "bench"
                            for args, cwd in clippy))

    def test_the_library_is_built_in_release_for_every_target(self):
        calls = []
        with mock.patch.dict(os.environ, LINT=json.dumps(LINT)), \
                mock.patch.object(rust_lint, "cargo", lambda args, cwd: calls.append((args, cwd))):
            rust_lint.run("library")
        builds = [args for args, cwd in calls if args[0] == "build" and cwd == CI.parent]
        self.assertEqual(len(builds), 1)
        (build,) = builds
        self.assertIn("--release", build)
        self.assertIn("--lib", build)
        # All targets in one run (see ci/rust_lint.py).
        self.assertEqual([build[i + 1] for i, a in enumerate(build) if a == "--target"],
                         [e["target"] for e in LINT])

    def test_the_image_has_every_targets_standard_library(self):
        # The lint image's toolchain (ci/runner.Dockerfile's amd64 case), so
        # that its jobs download nothing until stable changes.
        text = (CI / "runner.Dockerfile").read_text()
        m = re.search(r"amd64\) host=(\S+?);[^\n]* \\\n\s+targets=(\S+?) ;;", text)
        self.assertIsNotNone(m)
        host, targets = m.group(1), m.group(2).split(",")
        self.assertEqual(sorted([host, *targets]), sorted(e["target"] for e in LINT))


if __name__ == "__main__":
    unittest.main()
