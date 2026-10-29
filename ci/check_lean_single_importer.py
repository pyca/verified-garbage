#!/usr/bin/env python3
"""Checks that a pull request adds no proof module that only one other proof
module imports (CLAUDE.md, "Lean modules"). Exits non-zero on violations,
naming each.

Every module is a `lean` process of its own that imports its whole closure
first: about a second of CI's time each, which in many modules is more than
the module's own work. A module whose one importer rebuilds whenever it
changes anyway gains nothing from being separate, so its contents belong in
that importer. Only the modules a change adds are checked, against
`--base` (default `HEAD^`: in CI, a pull request's merge commit's first
parent, the base branch, as for a merge queue's commit), so that those
already in the tree fail nothing until they are folded.

A new module is allowed when:

  * another module, or none yet, imports it, or its one importer is not a
    proof module (a registration, variant or test file), or imports it
    `meta` or `all`;
  * it is a module that exists by a convention of CLAUDE.md: under
    `Proof/Framework/` or `Proof/Variants/`, a `*Lit` or `Instances`
    module, one that runs at elaboration time (`meta`), or one whose
    results others are meant to share (`materialize_*`, `taint_summary`);
  * it says why it is separate in a line `-- separate module: <why>`, e.g.
    that its proofs cost more than its imports (`ci/lean_profile.py`), so
    that keeping them apart spares its importer's changes from re-checking
    them.

    python3 ci/check_lean_single_importer.py [--base REV]
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

IMPORT = re.compile(r"(public\s+)?(meta\s+)?import\s+(all\s+)?([\w.]+)")
MARKER = re.compile(r"^--\s*separate module:\s*\S", re.M)
SHARED = re.compile(r"\bmaterialize_\w+|\btaint_summary\b|^\s*(?:public\s+)?meta\s+(?:section|import)\b", re.M)
CONVENTION_DIRS = ("VerifiedGarbage.Proof.Framework.", "VerifiedGarbage.Proof.Variants.")


def header(text: str) -> list[tuple[str, bool]]:
    """The imports of a file: (module, whether `meta` or `all`), reading only
    its header."""
    out, comment = [], False
    for line in text.splitlines():
        s = line.strip()
        if comment:
            comment = "-/" not in s
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = "-/" not in s[2:]
            continue
        if not s or s.startswith("--") or s in ("module", "prelude"):
            continue
        m = IMPORT.match(s)
        if not m:
            break
        out.append((m.group(4), bool(m.group(2) or m.group(3))))
    return out


def module_name(rel: str) -> str:
    return rel.removesuffix(".lean").replace("/", ".")


def is_proof(mod: str) -> bool:
    return mod.startswith("VerifiedGarbage.Proof.")


def problems(lean: pathlib.Path, added: set[str]) -> list[str]:
    """What is wrong with the modules `added` (names) under `lean`, the
    directory with `VerifiedGarbage/`, one line each."""
    candidates = {}
    for mod in sorted(added):
        if not is_proof(mod) or mod.startswith(CONVENTION_DIRS):
            continue
        last = mod.rsplit(".", 1)[1]
        if last.endswith("Lit") or last == "Instances":
            continue
        f = lean / (mod.replace(".", "/") + ".lean")
        if not f.exists():
            continue
        text = f.read_text(encoding="utf-8")
        if MARKER.search(text) or SHARED.search(text):
            continue
        candidates[mod] = []
    if not candidates:
        return []
    for root in ("VerifiedGarbage", "VerifiedGarbageTest"):
        for f in (lean / root).rglob("*.lean"):
            mod = module_name(f.relative_to(lean).as_posix())
            for imp, special in header(f.read_text(encoding="utf-8")):
                if imp in candidates:
                    candidates[imp].append((mod, special))
    for f in lean.glob("*.lean"):  # the emitter's drivers
        for imp, special in header(f.read_text(encoding="utf-8")):
            if imp in candidates:
                candidates[imp].append((f.stem, special))
    out = []
    for mod, importers in sorted(candidates.items()):
        if len(importers) != 1:
            continue
        importer, special = importers[0]
        if special or not is_proof(importer):
            continue
        rel = mod.replace(".", "/") + ".lean"
        out.append(f"lean/{rel}: new module imported only by {importer}: put its contents there, "
                   f"or say why it is separate in a line `-- separate module: <why>` "
                   f"(CLAUDE.md, \"Lean modules\")")
    return out


def added_modules(base: str) -> set[str]:
    """The modules under lean/VerifiedGarbage/ added since `base`, in the
    working tree (untracked files too); renamed files are not new."""
    def git(*args):
        return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True,
                              text=True).stdout.split()
    files = git("diff", "--diff-filter=A", "-M", "--name-only", base, "--", "lean/VerifiedGarbage")
    files += git("ls-files", "--others", "--exclude-standard", "--", "lean/VerifiedGarbage")
    return {module_name(f.removeprefix("lean/")) for f in files if f.endswith(".lean")}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--base", default="HEAD^", help="the revision to compare with (default HEAD^)")
    args = parser.parse_args(argv)
    found = problems(LEAN, added_modules(args.base))
    for p in found:
        print(p, file=sys.stderr)
    if found:
        return 1
    print("No new single-importer proof modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
