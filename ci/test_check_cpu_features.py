"""The native path must exercise exactly the masked emulated feature set."""

import json
import os
import pathlib
import subprocess
import tempfile
import textwrap
import unittest

from cpu_features import select


class SelectionTests(unittest.TestCase):
    def test_missing_feature_falls_back(self):
        self.assertEqual(
            select("avx,avx2", "avx,avx2,sha512", ""),
            ("sde", "avx,avx2,sha512"),
        )

    def test_mask_can_run_natively_when_full_model_cannot(self):
        self.assertEqual(
            select("avx,avx2", "avx,avx2,sha512", "avx,avx2"),
            ("native", "avx,avx2"),
        )

    def test_newer_host_is_restricted_to_model(self):
        self.assertEqual(
            select("avx,avx2,sha512", "avx,avx2", ""),
            ("native", "avx,avx2"),
        )

    def test_features_absent_from_model_stay_absent(self):
        self.assertEqual(select("aes,sha", "aes", "aes,sha"), ("native", "aes"))

    def test_baseline_is_explicitly_none(self):
        self.assertEqual(select("aes,sha", "", ""), ("native", "none"))
        self.assertEqual(select("aes", "aes,sha", "none"), ("native", "none"))
        self.assertEqual(select("sha", "sha", "aes"), ("native", "none"))


class WorkflowTests(unittest.TestCase):
    def run_workflow(self, fail_mode="", force_fallback=False):
        root = pathlib.Path(__file__).resolve().parent.parent
        workflow = (root / ".github/workflows/ci.yml").read_text()
        body = workflow.split("      - name: Test the implementations\n", 1)[1]
        script = textwrap.dedent(body.split("        run: |\n", 1)[1].split("        env:\n", 1)[0])
        with tempfile.TemporaryDirectory() as directory:
            temp = pathlib.Path(directory)
            cargo = temp / "cargo"
            cargo.write_text(textwrap.dedent('''\
                #!/usr/bin/env python3
                import json, os, sys
                runner = os.environ.get("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER", "")
                args = sys.argv[1:]
                mode = "build" if "--no-run" in args else "cpu" if "--lib" in args else "sde" if runner else "native"
                with open(os.environ["CALLS"], "a") as output:
                    output.write(json.dumps([mode, os.environ.get("VG_CPU_FEATURES"), args]) + "\\n")
                sys.exit(int(mode == os.environ["FAIL_MODE"]))
                '''))
            cargo.chmod(0o755)
            env = dict(os.environ)
            env.pop("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER", None)
            env.update(
                PATH=f"{temp}{os.pathsep}{env['PATH']}",
                RUNNER_TEMP=str(temp),
                CALLS=str(temp / "calls"),
                FAIL_MODE=fail_mode,
                CHIP="arl",
                HOST_CPU_FEATURES="avx,avx2",
                MODEL_CPU_FEATURES="avx,avx2,sha512",
                RUNS="- | sha512 cpu\navx,avx2 | sha512 cpu",
            )
            if force_fallback:
                env.update(
                    HOST_CPU_FEATURES="avx,avx2,sha512",
                    RUNS="avx,avx2,sha512 | sha512 cpu | fallback",
                )
            result = subprocess.run(
                ["bash", "-eo", "pipefail", "-c", script],
                cwd=root, env=env, text=True, capture_output=True, timeout=20,
            )
            calls = [json.loads(line) for line in (temp / "calls").read_text().splitlines()]
        return result, calls

    def test_mixed_native_and_fallback_preserve_cpu_checks(self):
        result, calls = self.run_workflow()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertCountEqual([call[0] for call in calls], ["build", "native", "sde", "cpu"])
        native = next(call for call in calls if call[0] == "native")
        self.assertEqual(native[1], "avx,avx2")
        self.assertEqual(native[2][-2:], ["--skip", "cpu::"])
        cpu = next(call for call in calls if call[0] == "cpu")
        self.assertEqual(cpu[1], native[1])
        self.assertEqual(cpu[2][-1], "cpu::")
        fallback = next(call for call in calls if call[0] == "sde")
        self.assertEqual(fallback[1], "avx,avx2,sha512")
        self.assertEqual(fallback[2][-2:], ["sha512", "cpu"])

    def test_successful_cpu_check_cannot_hide_native_failure(self):
        result, calls = self.run_workflow("native")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cpu", [call[0] for call in calls])

    def test_cpu_or_fallback_failure_fails_job(self):
        for mode in ["cpu", "sde"]:
            with self.subTest(mode=mode):
                result, _ = self.run_workflow(mode)
                self.assertNotEqual(result.returncode, 0)

    def test_fallback_check_uses_sde_even_on_capable_host(self):
        result, calls = self.run_workflow(force_fallback=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([call[0] for call in calls], ["build", "sde"])
        self.assertEqual(calls[1][1], "avx,avx2,sha512")
        self.assertIn("simulated missing host features", result.stdout)


if __name__ == "__main__":
    unittest.main()
