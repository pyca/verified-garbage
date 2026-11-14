#!/usr/bin/env python3
"""Checks that `ci/residue_allowlist.txt` only shrinks.

The list names the functions that do not yet prove they return without
secret residue (`Artifact.residue`, `lean/VerifiedGarbage/TCB/X86_64/Residue.lean`).
The emitter refuses a function of a target that defines it with no proof
unless the list names it, and a line that names no such function
(`Rust.checkResidue`). This script refuses a line that the revision `--base`
(default `HEAD^`: in CI, a pull request's merge commit's first parent, the
base branch) does not have: a new function proves it, rather than joining
the list, which is burned down as functions are converted.

    python3 ci/check_residue_allowlist.py [--base REV]
"""

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIST = "ci/residue_allowlist.txt"


def entries(text: str) -> set[str]:
    """The list's lines, as the emitter reads them (`parseResidueAllowlist`):
    but blank lines and comments, with their words joined by one space."""
    out = set()
    for line in text.splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            out.add(" ".join(line.split()))
    return out


def added(base: str, head: str) -> list[str]:
    """The entries of `head` that `base` does not have, in order."""
    return sorted(entries(head) - entries(base))


def base_text(rev: str) -> str | None:
    """The list at `rev`, or `None` if it has none (the change adds it)."""
    p = subprocess.run(["git", "show", f"{rev}:{LIST}"], cwd=ROOT, capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else None


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default="HEAD^", help="the revision to compare with (default HEAD^)")
    args = parser.parse_args(argv)
    base = base_text(args.base)
    if base is None:
        return 0
    new = added(base, (ROOT / LIST).read_text())
    for e in new:
        print(f"{LIST}: `{e}` is new: prove that the function returns without secret residue "
              "(`Registration.residue`) instead of listing it", file=sys.stderr)
    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
