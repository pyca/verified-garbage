#!/usr/bin/env python3
"""Checks that the definitions of proof modules are `noncomputable` (draft,
prototype for branch `lean-cache-noncomputable`). Exits non-zero on
violations, naming each.

Lean compiles every computable definition to IR, C and LCNF data stored in
the module's `.olean` and `.olean.private`, which the build cache ships for
every module, though nothing runs most of what proof modules define (the
witness states, contracts and region helpers of a proof). `noncomputable
section` does not stop this: it only silences the definitions that fail to
compile. A definition is left out of the compiler only when it is itself
`noncomputable`.

Every top-level `def`, `abbrev` and `instance` of the directories in `SCOPE`
must be `noncomputable` (or `meta`, which runs at elaboration time), unless
the line before it says why it must stay computable,
`-- computable: <why>`: something evaluates it as compiled code, such as
`taint_decide`, `materialize_*` or the emitter (through a registration's
artifacts). The build finds those: a computable definition using a
`noncomputable` one, or a tactic evaluating one, fails with "failed to
compile definition, consider marking it as 'noncomputable' because it
depends on 'X'".

    python3 ci/check_lean_noncomputable.py [DIR ...]
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

# Directories (relative to `lean/`) whose proof modules are checked, while
# the rule is adopted one algorithm at a time.
SCOPE = ["VerifiedGarbage/Proof/Rc2"]

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public)\s+)*"
    r"(noncomputable\s+|meta\s+)?(?:(?:private|protected)\s+)*(def|abbrev|instance)\b(.*)")
MARKER = re.compile(r"^--\s*computable:\s*\S")


def violations(path: pathlib.Path) -> list[str]:
    out = []
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m or m.group(1):
            continue
        if i > 0 and MARKER.match(lines[i - 1]):
            continue
        out.append(f"{path.relative_to(ROOT)}:{i + 1}: {line.strip()[:100]}")
    return out


def main(argv: list[str]) -> int:
    dirs = [LEAN / d for d in (argv or SCOPE)]
    bad = [v for d in dirs for p in sorted(d.rglob("*.lean")) for v in violations(p)]
    for v in bad:
        print(v)
    if bad:
        print(f"{len(bad)} computable definitions in proof modules: mark them `noncomputable`, "
              "or say why they must stay computable in a line `-- computable: <why>` before "
              "them (ci/check_lean_noncomputable.py)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
