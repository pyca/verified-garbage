"""The split of `rust-cpu-features`' runs across shards, and the workflow step
that runs a shard's lines (with a stand-in for `cargo`)."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

import cpu_shards

CI = Path(__file__).resolve().parent
WORKFLOW = CI.parent / ".github/workflows/ci.yml"

RUNS = """\
- | x25519 rsa cpu
avx,avx2 | rsa_pkcs1 cpu
avx,bmi1 | rsa_pss cpu
aes,vaes | aes_gcm cpu

aes,vpclmulqdq | aes_gcm cpu
pclmulqdq | aes_gcm cpu
"""


def workflow_runs(chip):
    """The `runs` of `chip`'s first matrix entry in ci.yml."""
    text = WORKFLOW.read_text()
    entry = text.split(f"          - chip: {chip}\n", 1)[1]
    block = entry.split("|\n", 1)[1]
    lines = []
    for line in block.splitlines():
        if not line.startswith("              "):
            break
        lines.append(line.strip())
    return "\n".join(lines)


class SplitTests(unittest.TestCase):
    def shards(self, n, times=None, runs=RUNS):
        return [cpu_shards.pick("icx", f"{i}/{n}", {"icx": {"no-avx512f": times or {}}}, runs)
                for i in range(1, n + 1)]

    def test_every_line_runs_once(self):
        lines = cpu_shards.parse_runs(RUNS)
        for n in range(1, len(lines) + 1):
            shards = self.shards(n)
            self.assertEqual(sorted(sum(shards, [])), sorted(lines))
            self.assertTrue(all(shards))

    def test_slow_lines_get_their_own_shards(self):
        times = {"-": 290, "avx,avx2": 301, "avx,bmi1": 303,
                 "aes,vaes": 5, "aes,vpclmulqdq": 18, "pclmulqdq": 12}
        shards = self.shards(3, times)
        self.assertEqual(sorted(s[0][0] for s in shards), ["-", "avx,avx2", "avx,bmi1"])
        # The fast lines go to the least loaded shards: the slowest of them
        # to the shard of the fastest slow line.
        self.assertEqual(shards[2], [("-", "x25519 rsa cpu"), ("aes,vpclmulqdq", "aes_gcm cpu")])

    def test_lines_without_a_time_count_as_the_median(self):
        times = {"-": 100, "avx,avx2": 1, "avx,bmi1": 1, "aes,vaes": 1}
        shards = self.shards(2, times)
        # 100 alone; the others (1 each, the unknown ones the median, 1).
        self.assertEqual(shards[0], [("-", "x25519 rsa cpu")])
        self.assertEqual(len(shards[1]), 5)

    def test_slowest_first(self):
        times = {"aes,vaes": 5, "pclmulqdq": 9, "-": 1, "avx,avx2": 2, "avx,bmi1": 2, "aes,vpclmulqdq": 3}
        (only,) = self.shards(1, times)
        self.assertEqual([f for f, _ in only],
                         ["pclmulqdq", "aes,vaes", "aes,vpclmulqdq", "avx,avx2", "avx,bmi1", "-"])

    def test_other_cpus_times_are_not_used(self):
        self.assertEqual(cpu_shards.pick("icx", "1/2", {"skx": {"no-avx512f": {"pclmulqdq": 99}}}, RUNS),
                         cpu_shards.pick("icx", "1/2", {}, RUNS))

    def test_cpu_key_ignores_empty_fields(self):
        self.assertEqual(cpu_shards.cpu_key("icx  "), "icx")
        self.assertEqual(cpu_shards.cpu_key(" native x86_64 "), "native x86_64")

    def test_no_shard_is_every_line(self):
        self.assertEqual(cpu_shards.pick("icx", "", {}, RUNS), self.shards(1)[0])

    def test_errors(self):
        with self.assertRaisesRegex(SystemExit, "twice"):
            cpu_shards.parse_runs("a | x\n a  | y\n")
        with self.assertRaisesRegex(SystemExit, "some would run nothing"):
            cpu_shards.pick("icx", "1/7", {}, RUNS)
        with self.assertRaisesRegex(SystemExit, "not between"):
            cpu_shards.parse_shard("4/3")

    def test_times_and_merge(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as f:
            f.write("-\t1.25 0.5\navx,avx2\t3 1\n\n")
        try:
            a = cpu_shards.times("icx  ", "avx512f", Path(f.name).read_text())
        finally:
            os.unlink(f.name)
        self.assertEqual(a, {"icx": {"avx512f": {"-": 1.75, "avx,avx2": 4.0}}})
        # Later parts win, line by line, within each class of host.
        b = {"icx": {"avx512f": {"-": 2.0}, "no-avx512f": {"-": 9.0}}, "skx": {"no-avx512f": {"-": 1.0}}}
        self.assertEqual(cpu_shards.merge([a, b]), {
            "icx": {"avx512f": {"-": 2.0, "avx,avx2": 4.0}, "no-avx512f": {"-": 9.0}},
            "skx": {"no-avx512f": {"-": 1.0}},
        })
        with self.assertRaisesRegex(SystemExit, "not one of"):
            cpu_shards.times("icx", "fast", "")

    def split_with(self, by_host):
        return [cpu_shards.pick("icx", f"{i}/3", {"icx": by_host}, RUNS) for i in (1, 2, 3)]

    def test_one_class_of_host_only(self):
        # Shard 1 of main's run had AVX-512, so its RSA line ("-") measured
        # five times faster; the slow hosts' times, which time every line,
        # are the ones used, not a mix.
        slow = {"-": 300, "avx,avx2": 301, "avx,bmi1": 303,
                "aes,vaes": 5, "aes,vpclmulqdq": 18, "pclmulqdq": 12}
        fast = {"-": 60, "aes,vaes": 4}
        self.assertEqual(self.split_with({"no-avx512f": slow, "avx512f": fast}),
                         self.split_with({"no-avx512f": slow}))
        # A mix would have put every light line with "-".
        mixed = dict(slow, **fast)
        self.assertEqual(len(self.split_with({"no-avx512f": mixed})[2]), 4)

    def test_the_class_timing_the_most_lines_without_a_complete_slow_one(self):
        fast = {"-": 60, "avx,avx2": 61, "avx,bmi1": 62, "aes,vaes": 1, "aes,vpclmulqdq": 1}
        slow = {"-": 300, "pclmulqdq": 30}
        self.assertEqual(self.split_with({"no-avx512f": slow, "avx512f": fast}),
                         self.split_with({"avx512f": fast}))
        # The slow hosts' on a tie.
        slow = {"-": 300, "avx,avx2": 1, "avx,bmi1": 1, "aes,vaes": 1, "aes,vpclmulqdq": 1}
        self.assertEqual(self.split_with({"no-avx512f": slow, "avx512f": fast}),
                         self.split_with({"no-avx512f": slow}))

    def test_icx_shards_each_get_an_rsa_line_before_any_time(self):
        runs = workflow_runs("icx")
        shards = self.shards(3, runs=runs)
        rsa = [[f for f, t in s if "rsa" in t] for s in shards]
        self.assertEqual([len(r) for r in rsa], [1, 1, 1])


class StepTests(unittest.TestCase):
    """The workflow's `Test the implementations` step, with a `cargo` that
    records what it ran and fails for one line."""

    @classmethod
    def setUpClass(cls):
        step = WORKFLOW.read_text().split("      - name: Test the implementations\n", 1)[1]
        script = step.split("        run: |\n", 1)[1].split("\n        env:\n", 1)[0]
        cls.script = textwrap.dedent(script)

    def run_step(self, shard, times="{}"):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ci").symlink_to(CI)
            bin_ = root / "bin"
            bin_.mkdir()
            cargo = bin_ / "cargo"
            cargo.write_text(
                "#!/bin/sh\n"
                "echo \"VG_CPU_FEATURES=${VG_CPU_FEATURES-unset} $*\" >> \"$CALLS\"\n"
                "[ \"$VG_CPU_FEATURES\" != pclmulqdq ]\n")
            cargo.chmod(0o755)
            (root / "temp").mkdir()
            env = dict(os.environ, PATH=f"{bin_}:{os.environ['PATH']}", RUNNER_TEMP=str(root / "temp"),
                       CALLS=str(root / "calls"), RUNS=RUNS, CPU="icx  ", SHARD=shard, TIMES=times,
                       JOB="4")
            result = subprocess.run(["bash", "-eo", "pipefail", "-c", self.script], cwd=root, env=env,
                                    capture_output=True, text=True)
            calls = (root / "calls").read_text().splitlines()
            out = root / "cpu-features-times-4.json"
            recorded = json.loads(out.read_text()) if out.exists() else None
            return result, calls, recorded

    def test_runs_its_lines_and_records_their_times(self):
        times = json.dumps({"icx": {"no-avx512f": {"-": 50, "avx,avx2": 40, "avx,bmi1": 30,
                                                   "aes,vaes": 1, "aes,vpclmulqdq": 1, "pclmulqdq": 1}}})
        result, calls, recorded = self.run_step("1/3", times)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls[0], "VG_CPU_FEATURES=unset test --locked --features cpu-features-env --no-run")
        # The slowest line alone: the others fill the other two shards first.
        self.assertEqual(calls[1:], [
            "VG_CPU_FEATURES= test --locked --features cpu-features-env -- x25519 rsa cpu",
        ])
        (host,) = recorded["icx"]
        self.assertIn(host, cpu_shards.HOSTS)
        self.assertEqual(sorted(recorded["icx"][host]), ["-"])
        self.assertIn("s of CPU (user, system)", result.stdout)

    def test_a_failing_line_fails_the_step_after_the_others(self):
        result, calls, recorded = self.run_step("")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("::error::Failed with VG_CPU_FEATURES=pclmulqdq: aes_gcm cpu", result.stdout)
        self.assertEqual(len(calls), 1 + 6)
        (lines,) = recorded["icx"].values()
        self.assertEqual(len(lines), 6)


if __name__ == "__main__":
    unittest.main()
