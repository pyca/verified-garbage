#!/usr/bin/env python3
"""Exports the coverage of an instrumented `cargo test` run as an lcov file.

Adapted from `process_rust_coverage` in pyca/cryptography's noxfile.py.

Usage: run `cargo test` with `RUSTFLAGS=-Cinstrument-coverage` and
`LLVM_PROFILE_FILE=<dir>/cov-%p-%m.profraw`, then, from the repository root
and with the same `RUSTFLAGS` and Cargo feature options (e.g. `--features
cpu-features-env`, after the directory):

    python3 ci/export_rust_coverage.py <dir> [<cargo test options>...]

This writes `<arch>-<uuid>.lcov` in the current directory, where `<arch>`
is the `target_arch` the tests were built for, containing only this
repository's files, with repository-relative `/`-separated paths, so lcov
files from different platforms can be merged by `ci/merge_rust_coverage.py`,
which also checks each architecture's alone. A file may have a record for
each test binary; the merge sums them.

Two options may come before the Cargo options:

* `--cargo-dir <dir>` lists the test binaries of the `cargo test` run in
  `<dir>`, another workspace (the rustls checkout whose API tests run the
  rustls provider), rather than in this one;
* `--only <prefix>` keeps only the files under `<prefix>` (the rustls
  provider's, `crates/rustls-verified-garbage/`): the library's tests cover
  the library, and a run that tests only the provider must not count the
  library lines it builds but does not test.
"""

import json
import os
import pathlib
import subprocess
import sys
import uuid

EXE = ".exe" if sys.platform == "win32" else ""


def test_binaries(cargo_args: list[str], cargo_dir: str | None = None) -> list[str]:
    # `cargo test` has already built these; this only lists them.
    out = subprocess.run(
        ["cargo", "test", "--locked", "--no-run", "--message-format=json", *cargo_args],
        check=True,
        capture_output=True,
        text=True,
        cwd=cargo_dir,
    ).stdout
    binaries = []
    for line in out.splitlines():
        msg = json.loads(line)
        if (
            msg.get("reason") == "compiler-artifact"
            and msg["profile"]["test"]
            and msg.get("executable")
        ):
            binaries.append(msg["executable"])
    return binaries


def relative_records(lcov: str, root: pathlib.Path, only: str = "") -> str:
    """Keeps only records for files under `root` (and its `only`), with
    relative paths."""
    out = []
    for record in lcov.replace("\r\n", "\n").split("end_of_record\n"):
        lines = record.strip().splitlines()
        if not lines:
            continue
        assert lines[0].startswith("SF:"), lines[0]
        path = (root / lines[0][len("SF:") :]).resolve()
        try:
            rel = path.relative_to(root)
        except ValueError:
            continue  # the standard library or a dependency
        if rel.parts[0] == "target" or not rel.as_posix().startswith(only):
            continue
        out.append("\n".join([f"SF:{rel.as_posix()}", *lines[1:], "end_of_record"]))
    return "".join(line + "\n" for line in out)


def target_arch() -> str:
    """The `target_arch` Cargo builds for: the host's, or that of
    `CARGO_BUILD_TARGET` (the ARMv7 image's cross-compilation)."""
    target = os.environ.get("CARGO_BUILD_TARGET")
    cfg = subprocess.run(
        ["rustc", "--print", "cfg", *(["--target", target] if target else [])],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    (arch,) = [line.split('"')[1] for line in cfg.splitlines() if line.startswith("target_arch=")]
    return arch


def main(profraw_dir: str, *args: str) -> None:
    root = pathlib.Path.cwd().resolve()
    cargo_args = list(args)
    cargo_dir = None
    only = ""
    while cargo_args[:1] in (["--cargo-dir"], ["--only"]):
        if cargo_args[0] == "--cargo-dir":
            cargo_dir = cargo_args[1]
        else:
            only = cargo_args[1]
        cargo_args = cargo_args[2:]
    libdir = subprocess.run(
        ["rustc", "--print", "target-libdir"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    bindir = pathlib.Path(libdir).parent / "bin"

    profraws = sorted(str(p) for p in pathlib.Path(profraw_dir).glob("*.profraw"))
    assert profraws, f"no .profraw files in {profraw_dir}"
    profdata = os.path.join(profraw_dir, "rust-cov.profdata")
    subprocess.run(
        [str(bindir / f"llvm-profdata{EXE}"), "merge", "-sparse", *profraws, "-o", profdata],
        check=True,
    )

    # One export per binary, never one export of them all (`-object` for each):
    # a function compiled into several binaries (a dependency's `#[inline]` or
    # generic function, instantiated in each) has a coverage record in each,
    # under the same name, and a binary that never calls it records 0. Given
    # them all, llvm-cov keeps the first binary's record and drops the others
    # ("functions have mismatched data"), so the counts depended on the order
    # of the binaries. `ci/merge_rust_coverage.py` sums the records of a file.
    records = []
    for binary in test_binaries(cargo_args, cargo_dir):
        lcov = subprocess.run(
            [
                str(bindir / f"llvm-cov{EXE}"),
                "export",
                binary,
                f"-instr-profile={profdata}",
                "--format=lcov",
            ],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        records.append(relative_records(lcov, root, only))

    out = f"{target_arch()}-{uuid.uuid4()}.lcov"
    with open(out, "w", newline="\n") as f:
        f.write("".join(records))
    print(f"wrote {out}")


if __name__ == "__main__":
    main(*sys.argv[1:])
