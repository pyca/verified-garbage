#!/usr/bin/env python3
"""Checks that the library is made of Lean modules (CLAUDE.md, "Lean
modules"). Exits non-zero on violations, naming each.

  * Every file under lean/VerifiedGarbage/ is a module (it starts with
    `module`, after any leading comment).

Lean checks the rest itself: a module may not import a file that is not
one ("cannot import non-`module`").
"""

import pathlib
import sys
from collections.abc import Iterable

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"


def is_module(lines: Iterable[str]) -> bool:
    """Whether `lines` start with `module`, after any leading comments. It
    reads only as far as the header, so that a file's proofs are not read."""
    comment = False
    for l in lines:
        s = l.strip()
        if comment:
            comment = not s.endswith("-/")
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
            continue
        if s == "module":
            return True
        if s and not s.startswith("--"):
            return False
    return False


def problems(lean: pathlib.Path) -> list[str]:
    """What is wrong under `lean` (the directory with `VerifiedGarbage/`), one
    line each."""
    out = []
    for f in sorted((lean / "VerifiedGarbage").rglob("*.lean")):
        rel = f.relative_to(lean).as_posix()
        with f.open(encoding="utf-8") as lines:
            if not is_module(lines):
                out.append(f"lean/{rel}: not a module; every file under lean/VerifiedGarbage/ "
                           "starts with `module` (CLAUDE.md, \"Lean modules\")")
    return out


def main() -> int:
    found = problems(LEAN)
    for p in found:
        print(p, file=sys.stderr)
    if not found:
        print("Lean modules OK")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
