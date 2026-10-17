"""The architectures a pull request's changes run the Rust tests of
(ci/rust_arches.py), and that ci.yml's Rust jobs read nothing it leaves out."""

from pathlib import Path
import re
import subprocess
import sys
import unittest

import rust_arches

CI = Path(__file__).resolve().parent
WORKFLOW = CI.parent / ".github/workflows/ci.yml"
ALL = ["aarch64", "arm", "x86", "x86_64"]

# The jobs that run or check the Rust tests.
RUST_JOBS = ("rust-arches", "rust", "rust-thumb", "cpu-features-times", "rust-cpu-features", "coverage")


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
                ]
            ),
            [],
        )

    def test_output(self):
        def run(args, stdin):
            return subprocess.run(
                [sys.executable, str(CI / "rust_arches.py"), *args],
                input=stdin, capture_output=True, text=True, check=True,
            ).stdout

        self.assertEqual(run([], "src/asm/arm/md5.rs\n\nlean/A.lean\n"), 'arches=["arm"]\nall=false\n')
        self.assertEqual(run([], ""), "arches=[]\nall=false\n")
        self.assertEqual(run([], "src/lib.rs\n"), f"arches={ALL}\nall=true\n".replace("'", '"'))
        self.assertEqual(run(["--all"], ""), run([], "src/lib.rs\n"))


class Workflow(unittest.TestCase):
    def test_rust_jobs_use_only_rust_scripts(self):
        for name in RUST_JOBS:
            text = job(name)
            with self.subTest(job=name):
                used = set(re.findall(r"ci/[A-Za-z0-9_.-]+", text))
                self.assertTrue(used <= rust_arches.RUST_CI, used - rust_arches.RUST_CI)
                self.assertNotIn(".github/actions/lean-", text)

    def test_matrix_arches(self):
        # Every entry of `rust` names its architecture, which `TESTS` reads.
        rust = job("rust")
        self.assertEqual(
            len(re.findall(r"^ +arch: (\S+)$", rust, flags=re.M)),
            len(re.findall(r"^ +(?:- )?os: ", rust, flags=re.M)),
        )
        for name in ("rust", "rust-cpu-features"):
            for arch in re.findall(r"^ +arch: (\S+)$", job(name), flags=re.M):
                self.assertIn(arch, ALL)


if __name__ == "__main__":
    unittest.main()
