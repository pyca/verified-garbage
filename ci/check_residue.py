#!/usr/bin/env python3
"""Checks which generated functions leave no residue (`Artifact.noResidue`).

Every function in src/asm/<target>/<module>.rs whose documentation lacks the
emitter's no-residue paragraph must be listed in
ci/residue_pending/<target>/<module>.txt (one name per line), and every name
listed there must be such a function. A module without a file has every
function proving it, so new modules, and new functions of other modules,
cannot be added without it.

With `--base REF` (CI passes the pull request's base), a name may be listed
only if REF lists it too: the lists only shrink, until they are gone and
`NoResidue` becomes part of `Verified`.

`--write` rewrites the lists from src/asm (removing a file that would be
empty); run it after a change that makes functions prove it.
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ASM = ROOT / "src" / "asm"
PENDING = ROOT / "ci" / "residue_pending"
MARK = "It leaves nothing secret in memory outside its buffers"
FN = re.compile(r"((?:^///.*\n)*)(?:^#\[.*\]\n)*^pub\(crate\) unsafe extern \"[^\"]+\" fn (\w+)", re.M)


def lacking():
    """For each (target, module), the functions without the paragraph."""
    out = {}
    for f in sorted(ASM.glob("*/*.rs")):
        if f.name == "mod.rs":
            continue
        names = [m.group(2) for m in FN.finditer(f.read_text()) if MARK not in m.group(1)]
        out[(f.parent.name, f.stem)] = names
    return out


def listed(read):
    """The pending lists, `read(path)` giving a file's text or None."""
    out = {}
    for (t, m) in lacking():
        text = read(f"ci/residue_pending/{t}/{m}.txt")
        if text is not None:
            out[(t, m)] = [l for l in text.split("\n") if l.strip()]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    have = lacking()
    if args.write:
        for (t, m), names in have.items():
            p = PENDING / t / f"{m}.txt"
            if names:
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("".join(n + "\n" for n in names))
            elif p.exists():
                p.unlink()
        return 0

    def here(path):
        p = ROOT / path
        return p.read_text() if p.exists() else None

    errors = []
    pend = listed(here)
    for f in PENDING.glob("*/*.txt"):
        if (f.parent.name, f.stem) not in have:
            errors.append(f"{f.relative_to(ROOT)}: no module src/asm/{f.parent.name}/{f.stem}.rs")
    for key, names in have.items():
        lst = set(pend.get(key, []))
        for n in names:
            if n not in lst:
                errors.append(f"{key[0]}/{key[1]}: {n} does not prove `noResidue` and is not pending")
        for n in lst - set(names):
            errors.append(f"{key[0]}/{key[1]}: {n} is pending but proves `noResidue` or is gone: "
                          "remove it (`--write`)")
    if args.base:
        def at_base(path):
            r = subprocess.run(["git", "show", f"{args.base}:{path}"], cwd=ROOT,
                               capture_output=True, text=True)
            return r.stdout if r.returncode == 0 else None
        base = listed(at_base)
        for key, names in pend.items():
            for n in set(names) - set(base.get(key, [])):
                errors.append(f"{key[0]}/{key[1]}: {n} is newly pending: a new function must "
                              "prove `noResidue`")
    for e in errors:
        print(e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
