"""Timing setup changes the test runner, never the compiler environment."""

import os
from pathlib import Path
import subprocess
import unittest


SETUP = Path(__file__).with_name("rust_test_timing.sh")
KEY = "CARGO_TARGET_THUMBV7NEON_UNKNOWN_LINUX_GNUEABIHF_RUNNER"


class TimingRunnerTests(unittest.TestCase):
    def run_setup(self, runner=""):
        env = {k: v for k, v in os.environ.items() if k != "RUSTC_BOOTSTRAP"}
        env.update(CARGO_BUILD_TARGET="thumbv7neon-unknown-linux-gnueabihf")
        env[KEY] = runner
        return subprocess.run(
            ["bash", "-ec", """source "$1"; test -z "${RUSTC_BOOTSTRAP+x}";
             runner=${!2}; $runner sh -c 'printf "%s:%s" "$RUSTC_BOOTSTRAP" "$1${EXISTING_RUNNER-}"; exit 7' _ "test argument"
             """,
             "bash", str(SETUP), KEY],
            env=env, capture_output=True, text=True,
        )

    def test_native_binary_gets_bootstrap_and_preserves_status_and_arguments(self):
        result = self.run_setup()
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(result.stdout, "1:test argument")

    def test_existing_cross_or_sde_runner_is_preserved(self):
        result = self.run_setup("env EXISTING_RUNNER=1")
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(result.stdout, "1:test argument1")


if __name__ == "__main__":
    unittest.main()
