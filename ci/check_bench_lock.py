#!/usr/bin/env python3
"""Checks that bench/Cargo.lock has one version of each library the
benchmarks compare with. bench/Cargo.toml names aws-lc-sys beside aws-lc-rs
(for what aws-lc-rs does not wrap), each with a version of its own: an
update of aws-lc-rs alone leaves the lock file with two aws-lc-sys, so two
AWS-LCs in the binary, and the benchmarks that call aws-lc-sys measure the
older one under the same name. Exits non-zero naming each such library.
"""

import pathlib
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The crates whose code the reference benchmarks time.
LIBRARIES = ("aws-lc-rs", "aws-lc-sys", "openssl", "openssl-sys")


def duplicates(lock: dict) -> dict[str, list[str]]:
    """The `LIBRARIES` that `lock` (a parsed Cargo.lock) has more than one
    version of, each with its versions."""
    versions: dict[str, list[str]] = {}
    for package in lock.get("package", []):
        if package["name"] in LIBRARIES:
            versions.setdefault(package["name"], []).append(package["version"])
    return {name: sorted(v) for name, v in sorted(versions.items()) if len(v) > 1}


def main() -> int:
    bad = duplicates(tomllib.loads((ROOT / "bench/Cargo.lock").read_text()))
    for name, versions in bad.items():
        print(
            f"bench/Cargo.lock: {name} is locked at {', '.join(versions)}: "
            "bench/Cargo.toml must ask for the one version the others depend on",
            file=sys.stderr,
        )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
