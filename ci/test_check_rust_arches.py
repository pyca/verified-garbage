"""The Rust jobs a CI run starts (ci/rust_arches.py), and that ci.yml's Rust
jobs read nothing it leaves out."""

import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib
import unittest

import rust_arches

CI = Path(__file__).resolve().parent
WORKFLOW = CI.parent / ".github/workflows/ci.yml"
ALL = ["aarch64", "arm", "x86", "x86_64"]
MATRIX = tomllib.loads((CI / "rust_matrix.toml").read_text())

# The jobs that run or check the Rust tests.
RUST_JOBS = ("rust-arches", "rust", "rust-thumb", "cpu-features-times", "rust-cpu-features", "rust-check",
             "coverage")


def job(name):
    """The text of the job `name` in ci.yml, without comments."""
    text = WORKFLOW.read_text()
    body = re.split(rf"^  {re.escape(name)}:\n", text, flags=re.M)[1]
    body = re.split(r"^  \S", body, flags=re.M)[0]
    return "\n".join(line for line in body.splitlines() if not line.strip().startswith("#"))


class Arches(unittest.TestCase):
    def test_one_architecture(self):
        self.assertEqual(rust_arches.arches(["src/asm/x86_64/md5.rs"]), ["x86_64"])
        self.assertEqual(rust_arches.arches(["src/asm/x86/md5.rs"]), ["x86"])
        self.assertEqual(
            rust_arches.arches(["src/asm/arm/md5.rs", "src/asm/aarch64/sha256.rs", "lean/X.lean"]),
            ["aarch64", "arm"],
        )

    def test_shared(self):
        for path in [
            "src/asm/mod.rs",
            "src/asm/riscv64/md5.rs",
            "src/md5.rs",
            "src/cpu.rs",
            "tests/main.rs",
            "vectors/sources/x.toml",
            "Cargo.toml",
            "Cargo.lock",
            ".github/workflows/ci.yml",
            ".github/actions/upload-artifact/action.yml",
            "ci/cpu_tests.py",
            "ci/rust_arches.py",
            "something/new",
        ]:
            with self.subTest(path=path):
                self.assertEqual(rust_arches.arches(["src/asm/x86/md5.rs", path]), ALL)

    def test_not_rust(self):
        self.assertEqual(
            rust_arches.arches(
                [
                    "lean/VerifiedGarbage/Proof/Md5/X86_64/Compress.lean",
                    "bench/benches/primitives/md5.rs",
                    "docs/algorithms/md5.toml",
                    "README.md",
                    "CLAUDE.md",
                    "ci/lean_speed_allowed.py",
                    "ci/test_check_lean_shards.py",
                    ".github/actions/lean-assemble/action.yml",
                    ".github/workflows/lean-cache.yml",
                    ".github/workflows/full-ci.yml",
                ]
            ),
            [],
        )

    def test_ci_files(self):
        self.assertEqual(rust_arches.arches(["ci/rust_matrix.toml"]), ALL)


def run(event, stdin=""):
    out = subprocess.run(
        [sys.executable, str(CI / "rust_arches.py"), event],
        input=stdin, capture_output=True, text=True, check=True,
    ).stdout
    return {k: json.loads(v) for k, v in (line.split("=", 1) for line in out.splitlines())}


class Output(unittest.TestCase):
    def test_one_architecture(self):
        out = run("pull_request", "src/asm/arm/md5.rs\n\nlean/A.lean\n")
        self.assertEqual(out["arches"], ["arm"])
        self.assertIs(out["all"], False)
        self.assertEqual([e["name"] for e in out["rust"]], ["Linux, ARMv7"])
        self.assertEqual(len(out["thumb"]), 1)
        # ARMv7's one CPU entry, the baseline with VG_CPU_FEATURES=none.
        self.assertEqual([e["arch"] for e in out["cpu"]], ["arm"])
        self.assertTrue(all(e["tests"] for job in ("rust", "thumb", "cpu") for e in out[job]))

    def test_x86_64_takes_the_sde_chips(self):
        out = run("pull_request", "src/asm/x86_64/md5.rs\n")
        self.assertEqual(out["thumb"], [])
        self.assertEqual({e.get("arch", "x86_64") for e in out["cpu"]}, {"x86_64"})
        self.assertIn("icx", {e["chip"] for e in out["cpu"]})
        self.assertEqual({e["rust"] for e in out["rust"]}, {"stable", "1.88", "beta", "nightly"})

    def test_nothing(self):
        out = run("pull_request", "lean/A.lean\n")
        self.assertEqual((out["arches"], out["all"]), ([], False))
        self.assertEqual((out["rust"], out["thumb"], out["cpu"]), ([], [], []))
        # Every target is still built.
        targets = [t for e in MATRIX["check"] for t in e["targets"]]
        self.assertEqual(out["check"], [{"targets": " ".join(targets)}])

    def test_merge_group_reads_paths(self):
        for paths in ("src/asm/arm/md5.rs\n", "lean/A.lean\n", "src/lib.rs\n", ""):
            with self.subTest(paths=paths):
                self.assertEqual(run("merge_group", paths), run("pull_request", paths))

    def test_check_builds_the_arches_not_tested(self):
        out = run("pull_request", "src/asm/x86_64/md5.rs\nsrc/asm/arm/md5.rs\n")
        targets = out["check"][0]["targets"].split()
        self.assertIn("aarch64-apple-darwin", targets)
        self.assertIn("i686-unknown-linux-gnu", targets)
        self.assertNotIn("x86_64-unknown-linux-gnu", targets)
        self.assertNotIn("armv7-unknown-linux-gnueabihf", targets)

    def test_benchmarks_alone(self):
        out = run("pull_request", "bench/benches/primitives/md5.rs\nlean/A.lean\n")
        self.assertEqual((out["arches"], out["all"]), ([], False))
        self.assertEqual((out["thumb"], out["cpu"]), ([], []))
        # The stable Linux entries of every architecture, linting only.
        self.assertEqual([e["name"] for e in out["rust"]],
                         ["Linux, x86-64", "Linux, x86", "Linux, AArch64", "Linux, ARMv7"])
        for e in out["rust"]:
            self.assertEqual((e["rust"], e["tests"], e["bench_only"]), ("stable", False, True))
        self.assertEqual({e["arch"] for e in out["rust"]}, set(ALL))

    def test_benchmarks_and_one_architecture(self):
        out = run("pull_request", "bench/Cargo.lock\nsrc/asm/arm/md5.rs\n")
        self.assertEqual(out["arches"], ["arm"])
        tested = [e for e in out["rust"] if e["tests"]]
        linted = [e for e in out["rust"] if not e["tests"]]
        self.assertEqual([e["name"] for e in tested], ["Linux, ARMv7"])
        self.assertTrue(all("bench_only" not in e for e in tested))
        # ARMv7's own entry lints the benchmarks already.
        self.assertEqual(sorted(e["arch"] for e in linted), ["aarch64", "x86", "x86_64"])
        self.assertTrue(all(e["bench_only"] for e in linted))

    def test_benchmarks_with_every_architecture(self):
        out = run("pull_request", "bench/Cargo.lock\nsrc/lib.rs\n")
        self.assertEqual(out, run("workflow_dispatch"))
        self.assertTrue(all("bench_only" not in e for e in out["rust"]))

    def test_every_job(self):
        full = run("workflow_dispatch")
        self.assertEqual(full, run("pull_request", "src/lib.rs\n"))
        self.assertEqual(full["check"], [])
        self.assertEqual((full["arches"], full["all"]), (ALL, True))
        # Every architecture has a job, and every job is in one of them.
        jobs = [e for job in ("rust", "thumb", "cpu") for e in full[job]]
        self.assertEqual({e.get("arch", "x86_64") for e in jobs}, set(ALL))
        self.assertTrue(all(e["tests"] for e in jobs))
        # The shards of a CPU, one entry each, with the same runs.
        icx = [e for e in full["cpu"] if e["chip"] == "icx"]
        self.assertEqual([e["shard"] for e in icx], ["1/2", "2/2"])
        self.assertEqual(len({e["runs"] for e in icx}), 1)
        self.assertTrue(all("shards" not in e for e in full["cpu"]))

    def test_push_builds_one_job_per_cache(self):
        push, full = run("push"), run("workflow_dispatch")
        self.assertEqual((push["arches"], push["all"]), ([], False))
        self.assertEqual(push["check"], [])
        for job in ("rust", "thumb"):
            self.assertEqual(push[job], [dict(e, tests=False) for e in full[job]])
        # The CPU jobs, which build the same tests, once per runner
        # architecture and container: the first of each.
        cpu = [dict(e, tests=False) for e in full["cpu"]]
        self.assertEqual(push["cpu"], [e for i, e in enumerate(cpu)
                                       if all(rust_arches.cache_of(e) != rust_arches.cache_of(d)
                                              for d in cpu[:i])])
        self.assertEqual({rust_arches.cache_of(e) for e in push["cpu"]},
                         {rust_arches.cache_of(e) for e in full["cpu"]})
        self.assertEqual({e.get("arch", "x86_64") for e in push["cpu"]},
                         {"x86_64", "x86", "aarch64", "arm"})
        self.assertEqual(len(push["cpu"]), 4)


class Workflow(unittest.TestCase):
    def test_rust_jobs_use_only_rust_scripts(self):
        for name in RUST_JOBS:
            text = job(name)
            with self.subTest(job=name):
                used = set(re.findall(r"ci/[A-Za-z0-9_.-]+", text))
                self.assertTrue(used <= rust_arches.RUST_CI, used - rust_arches.RUST_CI)
                self.assertNotIn(".github/actions/lean-", text)

    def test_matrix_arches(self):
        matrix = tomllib.loads((CI / "rust_matrix.toml").read_text())
        for job in ("rust", "thumb"):
            for entry in matrix[job]:
                self.assertIn(entry["arch"], ALL)
        for entry in matrix["cpu"]:
            self.assertIn(entry.get("arch", "x86_64"), ALL)
        self.assertEqual(sorted(e["arch"] for e in matrix["check"]), ALL)

    def test_jobs_read_their_matrices(self):
        for name, output in (("rust", "rust"), ("rust-thumb", "thumb"), ("rust-cpu-features", "cpu")):
            text = job(name)
            with self.subTest(job=name):
                self.assertIn(f"if: ${{{{ needs.rust-arches.outputs.{output} != '[]' }}}}", text)
                self.assertIn(f"include: ${{{{ fromJSON(needs.rust-arches.outputs.{output}) }}}}", text)
                self.assertIn("TESTS: ${{ matrix.tests }}", text)
        text = job("rust-check")
        self.assertIn("if: ${{ needs.rust-arches.outputs.check != '[]' }}", text)
        self.assertIn("include: ${{ fromJSON(needs.rust-arches.outputs.check) }}", text)

    def test_check_lints_only_what_the_tested_jobs_lint(self):
        # Otherwise a run that leaves an architecture out could fail on a
        # lint that a run testing it, a full run included, never runs.
        def lints(text):
            return {re.sub(r' --target "\$target"', "", line.strip())
                    for line in text.splitlines() if line.strip().startswith("cargo clippy")}
        check = lints(job("rust-check"))
        self.assertEqual(len(check), 3)
        for name in ("rust", "rust-thumb"):
            with self.subTest(job=name):
                self.assertLessEqual(check, lints(job(name)))

    def test_bench_only_lints_the_benchmarks_alone(self):
        text = job("rust")
        # rust_arches.is_bench_lint picks the entries this step runs on.
        self.assertIn("- name: Lint the benchmarks\n        if: ${{ matrix.rust == 'stable' && runner.os == 'Linux' }}", text)
        # Every architecture has one such entry.
        self.assertEqual(sorted(e["arch"] for e in MATRIX["rust"] if rust_arches.is_bench_lint(e)), ALL)
        # Every other step that builds or runs anything is off for it.
        self.assertIn("- name: Lint\n        if: ${{ matrix.rust == 'stable' && !matrix.bench_only }}", text)
        self.assertIn("- shell: bash\n        if: ${{ !matrix.bench_only }}\n        run: |\n          source ci/rust_test_timing.sh", text)
        self.assertNotIn("bench_only", job("rust-thumb") + job("rust-cpu-features"))

    def test_all_green_needs_every_rust_job(self):
        text = job("all-green")
        for name in RUST_JOBS:
            if name != "cpu-features-times":
                with self.subTest(job=name):
                    self.assertRegex(text, rf"needs: \[[^]]*\b{name}\b")


if __name__ == "__main__":
    unittest.main()
