"""The Rust jobs a CI run starts (ci/rust_arches.py), and that ci.yml's Rust
jobs read nothing it leaves out."""

import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib
import unittest

import bench_arches
import rust_arches

CI = Path(__file__).resolve().parent
WORKFLOW = CI.parent / ".github/workflows/ci.yml"
ALL = ["aarch64", "arm", "powerpc64", "riscv64", "x86", "x86_64"]

# The jobs that run or check the Rust tests.
RUST_JOBS = ("rust-arches", "rust", "rust-thumb", "rust-lint", "cpu-features-times", "rust-cpu-features",
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
        self.assertEqual(rust_arches.arches(["src/asm/powerpc64le/sha256.rs"]), ["powerpc64"])
        self.assertEqual(rust_arches.arches(["src/asm/riscv64/chacha20.rs"]), ["riscv64"])
        self.assertEqual(
            rust_arches.arches(["src/asm/arm/md5.rs", "src/asm/aarch64/sha256.rs", "lean/X.lean"]),
            ["aarch64", "arm"],
        )

    def test_one_architecture_crate(self):
        # A target's crate of generated code, its manifest too, is its own.
        self.assertEqual(rust_arches.arches(["crates/verified-garbage-asm-x86_64/src/md5.rs"]), ["x86_64"])
        self.assertEqual(rust_arches.arches(["crates/verified-garbage-asm-powerpc64le/Cargo.toml"]),
                         ["powerpc64"])
        # A new target's, every architecture's.
        self.assertEqual(rust_arches.arches(["crates/verified-garbage-asm-mips/src/lib.rs"]), ALL)
        # The crate of `Features`, every architecture's.
        self.assertEqual(rust_arches.arches(["crates/verified-garbage-cpu/src/lib.rs"]), ALL)

    def test_shared(self):
        for path in [
            "src/asm/mod.rs",
            "src/asm/mips64/md5.rs",
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
                    ".agents/skills/benchmarking/SKILL.md",
                    ".claude/skills",
                    "ci/lean_speed_allowed.py",
                    "ci/test_check_lean_shards.py",
                    ".github/actions/lean-assemble/action.yml",
                    ".github/workflows/lean-cache.yml",
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
        # ARMv7 and Thumb, each linted.
        self.assertEqual([e["target"] for e in out["lint"]],
                         ["armv7-unknown-linux-gnueabihf", "thumbv7neon-unknown-linux-gnueabihf"])

    def test_x86_64_takes_the_sde_chips(self):
        out = run("pull_request", "src/asm/x86_64/md5.rs\n")
        self.assertEqual(out["thumb"], [])
        self.assertEqual({e.get("arch", "x86_64") for e in out["cpu"]}, {"x86_64"})
        self.assertIn("icx", {e["chip"] for e in out["cpu"]})
        self.assertEqual({e["rust"] for e in out["rust"]}, {"stable", "1.95", "beta", "nightly"})

    def test_nothing(self):
        out = run("pull_request", "lean/A.lean\n")
        self.assertEqual((out["arches"], out["all"]), ([], False))
        self.assertEqual((out["rust"], out["thumb"], out["cpu"], out["lint"]), ([], [], [], []))

    def test_the_benchmarks_lint_every_target(self):
        out = run("pull_request", "bench/benches/primitives/md5.rs\n")
        self.assertEqual((out["arches"], out["rust"], out["thumb"], out["cpu"]), ([], [], [], []))
        self.assertEqual(out["lint"], run("merge_group")["lint"])

    def test_every_job(self):
        full = run("merge_group")
        self.assertEqual(full, run("pull_request", "src/lib.rs\n"))
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
        matrix = tomllib.loads((CI / "rust_matrix.toml").read_text())
        self.assertEqual(full["lint"], matrix["lint"])

    def test_bench_is_whether_the_benchmarks_measure_the_arch(self):
        for event in ("merge_group", "push"):
            out = run(event)
            with self.subTest(event=event):
                for e in out["rust"]:
                    self.assertEqual(e["bench"], e["arch"] in bench_arches.PLATFORMS, e["name"])
                self.assertEqual({e["arch"] for e in out["rust"] if not e["bench"]}, set())
                self.assertTrue(all("bench" not in e for job in ("thumb", "cpu") for e in out[job]))

    def test_push_builds_one_job_per_cache(self):
        push, full = run("push"), run("merge_group")
        self.assertEqual((push["arches"], push["all"]), ([], False))
        for job in ("rust", "thumb"):
            self.assertEqual(push[job], [dict(e, tests=False) for e in full[job]])
        self.assertEqual(push["lint"], full["lint"])
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

    def test_lint_has_every_platform(self):
        # A target of each platform the `rust` and `thumb` jobs build, and of
        # each Linux one, which lints the benchmarks.
        matrix = tomllib.loads((CI / "rust_matrix.toml").read_text())
        lint = {(e["arch"], e["target"]): e for e in matrix["lint"]}
        for entry in matrix["rust"]:
            os = entry["os"]
            system = "-pc-windows-" if os.startswith("windows") else "-apple-" if os.startswith("macos") else "-linux-"
            with self.subTest(entry=entry["name"]):
                found = [e for (arch, target), e in lint.items() if arch == entry["arch"] and system in target]
                self.assertTrue(found)
                if system == "-linux-":
                    self.assertTrue(any(e.get("bench") for e in found))
        for entry in matrix["thumb"]:
            self.assertIn((entry["arch"], "thumbv7neon-unknown-linux-gnueabihf"), lint)
        self.assertEqual(len(lint), len(matrix["lint"]))
        self.assertTrue(all(e["arch"] in ALL for e in matrix["lint"]))

    def test_only_rust_lint_runs_clippy_and_rustfmt(self):
        text = WORKFLOW.read_text()
        self.assertNotIn("cargo clippy", text)
        self.assertNotIn("cargo fmt", text)
        self.assertIn("python3 ci/rust_lint.py run", job("rust-lint"))
        self.assertIn("if: ${{ needs.rust-arches.outputs.lint != '[]' }}", job("rust-lint"))
        self.assertIn("LINT: ${{ needs.rust-arches.outputs.lint }}", job("rust-lint"))

    def test_rust_checkout_has_the_targets_functions(self):
        # The `rust` job checks out only `crates/verified-garbage-asm-<asm or
        # arch>/` (and every crate's manifest): that must
        # be the target directory whose architecture the entry tests.
        matrix = tomllib.loads((CI / "rust_matrix.toml").read_text())
        for entry in matrix["rust"]:
            with self.subTest(entry=entry["name"]):
                target = entry.get("asm", entry["arch"])
                self.assertEqual(rust_arches.ARCHES.get(target), entry["arch"])
        self.assertIn("/crates/verified-garbage-asm-${{ matrix.asm || matrix.arch }}/", job("rust"))
        self.assertIn("/crates/verified-garbage-asm-*/Cargo.toml", job("rust"))

    def test_only_benchmarked_arches_cache_the_benchmarks_dependencies(self):
        self.assertIn("if: ${{ matrix.bench && matrix.rust == 'stable' && runner.os == 'Linux' "
                      "&& github.event_name == 'push' }}", job("rust"))

    def test_jobs_read_their_matrices(self):
        for name, output in (("rust", "rust"), ("rust-thumb", "thumb"), ("rust-cpu-features", "cpu")):
            text = job(name)
            with self.subTest(job=name):
                self.assertIn(f"if: ${{{{ needs.rust-arches.outputs.{output} != '[]' }}}}", text)
                self.assertIn(f"include: ${{{{ fromJSON(needs.rust-arches.outputs.{output}) }}}}", text)
                self.assertIn("TESTS: ${{ matrix.tests }}", text)


if __name__ == "__main__":
    unittest.main()
