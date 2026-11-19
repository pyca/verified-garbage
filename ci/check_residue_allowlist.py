#!/usr/bin/env python3
"""Checks that `ci/residue_allowlist.txt` only shrinks.

The list names the functions that do not yet prove they return without
secret residue (`Verification.unscrubbed`, `lean/VerifiedGarbage/TCB/<ISA>/Residue.lean`).
The emitter refuses a function of a target that defines it with no proof
unless the list names it, and a line that names no such function
(`Rust.checkResidue`). This script refuses a line that the revision `--base`
(default `HEAD^`: in CI, a pull request's merge commit's first parent, the
base branch) does not have: a new function proves it, rather than joining
the list, which is burned down as functions are converted.

The one exception is a target that does not yet define it at `--base`
(whose `TCB/<ISA>/Target.lean` there sets no `noResidue`), as the list
began for x86-64: the change that makes the target define it lists every
function of the target at once, which from then on only shrinks.

    python3 ci/check_residue_allowlist.py [--base REV]
"""

import argparse
import pathlib
import re
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


def added(base: str, head: str, exempt: frozenset[str] = frozenset()) -> list[str]:
    """The entries of `head` that `base` does not have, in order, but those
    of the targets `exempt`."""
    return sorted(e for e in entries(head) - entries(base) if e.split(" ")[0] not in exempt)


def target_requires(text: str) -> tuple[str, bool] | None:
    """The name of the target a `TCB/<ISA>/Target.lean` defines, and whether
    it defines what it means to return without secret residue
    (`noResidue := some`), or `None` if it defines no target."""
    m = re.search(r"^@\[reducible\] def target : Target where\n((?:  .*\n)*)", text, re.M)
    if m is None:
        return None
    name = re.search(r'^  name := "([^"]+)"$', m.group(1), re.M)
    if name is None:
        return None
    return name.group(1), re.search(r"^  noResidue := some ", m.group(1), re.M) is not None


def unrequired(rev: str) -> frozenset[str]:
    """The targets of `rev` that do not define what it means to return
    without secret residue."""
    p = subprocess.run(["git", "ls-tree", "--name-only", f"{rev}:lean/VerifiedGarbage/TCB/"],
                       cwd=ROOT, capture_output=True, text=True, check=True)
    out = set()
    for d in p.stdout.split():
        f = subprocess.run(["git", "show", f"{rev}:lean/VerifiedGarbage/TCB/{d}/Target.lean"],
                           cwd=ROOT, capture_output=True, text=True)
        t = target_requires(f.stdout) if f.returncode == 0 else None
        if t is not None and not t[1]:
            out.add(t[0])
    return frozenset(out)


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
    new = added(base, (ROOT / LIST).read_text(), unrequired(args.base))
    for e in new:
        print(f"{LIST}: `{e}` is new: prove that the function returns without secret residue "
              "(`Verification.scrubbed`) instead of listing it", file=sys.stderr)
    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
