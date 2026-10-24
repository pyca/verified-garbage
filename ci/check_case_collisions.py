#!/usr/bin/env python3
"""Checks that no two tracked paths differ only in case. On a
case-insensitive filesystem (macOS's and Windows's defaults) such paths are
one file, so a checkout there loses one of them. Exits non-zero naming each
collision.
"""

import pathlib
import subprocess
import sys
from collections.abc import Iterable

ROOT = pathlib.Path(__file__).resolve().parent.parent


def collisions(paths: Iterable[str]) -> list[list[str]]:
    """The groups of `paths` that are the same path but for case: the files
    themselves, and the directories above them. Only the topmost of nested
    collisions is named (two directories `A/` and `a/`, not every path
    under them too)."""
    seen: dict[str, set[str]] = {}
    for p in paths:
        parts = p.split("/")
        for i in range(1, len(parts) + 1):
            prefix = "/".join(parts[:i])
            seen.setdefault(prefix.casefold(), set()).add(prefix)
    bad = {k for k, g in seen.items() if len(g) > 1}
    top = [
        k
        for k in bad
        if not any(k.startswith(o + "/") for o in bad)
    ]
    return sorted(sorted(seen[k]) for k in top)


def main() -> int:
    out = subprocess.run(
        ["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True
    ).stdout.decode()
    bad = collisions(p for p in out.split("\0") if p)
    for g in bad:
        print("paths that differ only in case: " + ", ".join(g), file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
