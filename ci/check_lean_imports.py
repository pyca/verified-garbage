#!/usr/bin/env python3
"""Checks the import discipline between the directories of
lean/VerifiedGarbage/, which keeps the trusted base small and separate from
proofs. Exits non-zero on violations.

  * TCB/   imports only Lean core and TCB/  (no Mathlib: smaller trusted base).
  * Spec/  imports only TCB/, Spec/ and Mathlib.
  * Impl/  imports only TCB/, Spec/, Impl/, Mathlib and Lean core's
    elaborator (`Lean.Elab`, for term elaborators that build tables:
    `Impl/NatPairs.lean`), never proofs.
  * A module of a target (one with a directory of TCB/, e.g. `Arm`, as a
    component of its path) imports no module of another target: a change
    to one target would rebuild the other's modules too, and a CI shard
    (ci/lean_shards.py), which builds a module with everything it imports,
    would check both. What more than one target uses goes in a
    target-independent module.
  * TCB/   holds definitions only: no `theorem` or `lemma` (CLAUDE.md), so
    that what is trusted is what is reviewed as trusted; lemmas about it go
    in Proof/.
"""

import pathlib
import re
import sys

from check_registrations import THEOREM, code_only

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean" / "VerifiedGarbage"

# The start of an import: `import`, and in a module `public`, `meta` and
# `all` imports.
IMPORT = r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?"

ALLOWED_IMPORTS = {
    "TCB": ("Lean", "VerifiedGarbage.TCB."),
    "Spec": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "Mathlib"),
    "Impl": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "VerifiedGarbage.Impl.", "Mathlib",
             "Lean.Elab"),
}


def allowed(mod: str, prefixes: tuple[str, ...]) -> bool:
    return any(mod == p or mod.startswith(p if p.endswith(".") else p + ".") for p in prefixes)


def target_of(parts, targets: set[str]) -> str | None:
    return next((p for p in parts if p in targets), None)


def tcb_lemmas(lean: pathlib.Path) -> list[str]:
    """A line for each theorem or lemma under `lean`'s (lean/VerifiedGarbage/'s)
    TCB/, outside comments and strings."""
    out = []
    for f in sorted((lean / "TCB").rglob("*.lean")):
        code = code_only(f.read_text())
        for m in THEOREM.finditer(code):
            line = code.count("\n", 0, m.start()) + 1
            out.append(f"{f.relative_to(lean.parent.parent)}:{line}: a {m.group(1)} in TCB/, "
                       "which holds definitions only; prove it under Proof/")
    return out


def main() -> int:
    errors = tcb_lemmas(LEAN)
    targets = {p.name for p in (LEAN / "TCB").iterdir() if p.is_dir()}
    for f in sorted(LEAN.rglob("*.lean")):
        own = target_of(f.relative_to(LEAN).with_suffix("").parts, targets)
        if own is None:
            continue
        for n, line in enumerate(f.read_text().splitlines(), 1):
            m = re.match(IMPORT + r"(VerifiedGarbage\.\S+)", line)
            other = m and target_of(m.group(1).split("."), targets)
            if other and other != own:
                errors.append(f"{f.relative_to(ROOT)}:{n}: a module of {own} may not import {m.group(1)}, of {other}")
    for d, prefixes in ALLOWED_IMPORTS.items():
        for f in sorted((LEAN / d).rglob("*.lean")):
            for n, line in enumerate(f.read_text().splitlines(), 1):
                m = re.match(IMPORT + r"(\S+)", line)
                if m and not allowed(m.group(1), prefixes):
                    errors.append(f"{f.relative_to(ROOT)}:{n}: {d}/ may not import {m.group(1)}")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("Lean imports OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
