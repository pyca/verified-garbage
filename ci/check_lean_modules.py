#!/usr/bin/env python3
"""Checks that the library is made of Lean modules (CLAUDE.md, "Lean
modules"). Exits non-zero on violations, naming each.

  * Every file under lean/VerifiedGarbage/ is a module (it starts with
    `module`, after any leading comment), except `Artifacts.lean`.
  * `Artifacts.lean` is not a module: it runs `#assert_standard_axioms`,
    which needs every proof, and a module sees the theorems it imports
    without their proofs (the audits refuse to run in one).
  * No module imports a file of this project that is not a module (Lean
    refuses).
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

# The one file of the library that is not a module.
NOT_MODULES = ["VerifiedGarbage/Artifacts.lean"]

ANY_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$", re.M)


def is_module(text: str) -> bool:
    """Whether `text` starts with `module`, after any leading comments."""
    comment = False
    for l in text.split("\n"):
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
    modules = {}
    for f in sorted((lean / "VerifiedGarbage").rglob("*.lean")):
        rel = f.relative_to(lean).as_posix()
        modules[rel] = is_module(f.read_text())
        if rel in NOT_MODULES and modules[rel]:
            out.append(f"lean/{rel}: a module, but it runs the audits, which need a file that is not one")
        elif rel not in NOT_MODULES and not modules[rel]:
            out.append(f"lean/{rel}: not a module; every file under lean/VerifiedGarbage/ but "
                       f"{', '.join(NOT_MODULES)} starts with `module` (CLAUDE.md, \"Lean modules\")")
    for rel, module in modules.items():
        if not module:
            continue
        for m in ANY_IMPORT.finditer((lean / rel).read_text()):
            dep = (m.group(1).replace(".", "/") + ".lean")
            if (lean / dep).exists() and not is_module((lean / dep).read_text()):
                out.append(f"lean/{rel}: a module, but imports `{m.group(1)}`, which is not one")
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
