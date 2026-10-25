#!/usr/bin/env python3
"""rustfmt and Clippy for every target of the Rust jobs, from one x86-64
Linux runner, in the lint image (`rust-lint` in ci.yml, ci/runner.Dockerfile).
`LINT` is the JSON list of the targets to lint, ci/rust_matrix.toml's `lint`
entries that ci/rust_arches.py keeps. Clippy only checks, so a target needs
its standard library and no linker. The library is linted for every target,
with each set of features its users build (`FEATURES`), all targets in one
run of Cargo, in parallel; the benchmarks for the targets with `bench`, whose
C cross compiler and OpenSSL the image has for the build scripts of AWS-LC
and OpenSSL's bindings, one target at a time: in one run, Cargo would enable
the features of a dependency for one target (aws-lc-sys's `all-bindings`, on
x86-64 and AArch64) on every target it builds.

  rust_lint.py targets library|benchmarks
      the crate's targets, comma-separated, for rustup
  rust_lint.py run library|benchmarks
      check the crate's formatting, then lint it for its targets
"""

import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

# The library's features, as its users enable them: none (but the default),
# `std`, and `cpu-features-env`, which also enables `std`.
FEATURES = ([], ["--features", "std"], ["--features", "cpu-features-env"])


def entries(crate):
    lint = json.loads(os.environ["LINT"])
    if crate == "library":
        return lint
    if crate == "benchmarks":
        return [e for e in lint if e.get("bench")]
    sys.exit(__doc__)


def cargo(args, cwd):
    print("+ cargo " + " ".join(args), flush=True)
    subprocess.run(["cargo", *args], cwd=cwd, check=True)


def run(crate):
    if crate == "library":
        targets = [arg for e in entries(crate) for arg in ("--target", e["target"])]
        cargo(["fmt", "--check"], ROOT)
        for features in FEATURES:
            cargo(["clippy", "--all-targets", "--locked", *targets, *features], ROOT)
        return
    cargo(["fmt", "--check"], ROOT / "bench")
    for e in entries(crate):
        cargo(["clippy", "--all-targets", "--locked", "--target", e["target"]], ROOT / "bench")


def main(argv):
    if len(argv) == 2 and argv[0] == "targets":
        print(",".join(e["target"] for e in entries(argv[1])))
    elif len(argv) == 2 and argv[0] == "run":
        run(argv[1])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
