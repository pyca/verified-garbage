#!/usr/bin/env python3
"""Lists the kernel checks that evaluate code without its literal, ranked by
what they cost the build: a tool for speeding up proofs, not a CI check.

`lit_decide`, `taint_decide` and the registrations' default proofs read the
literal of code (`materialize_code`, `Proof/Framework/Lit.lean`) only if the
module sees it: imports it, or imports a module that `public import`s it.
Otherwise the kernel builds the code again, from the functions that build
it, in every check (.agents/skills/proof-performance/SKILL.md, "Code
without its literal").

For each target, this runs `lean/CheckLitImports.lean` over the target's
registration files (`Artifacts/`, `Generic/`, `Variants/`), which lists each
proposition the kernel decides that reaches code with a literal the module
could import, and weighs each by the build's profile (`lean_profile.py`, so
restore the CI cache or build first): the kernel time of the declaration,
and that of the literal's own `lit_eq` (what evaluating the code once costs,
roughly what the check spends building it again).

Each line is a declaration, its kernel time, and the literals it evaluates
without, each with its `lit_eq` time and module:

  unseen  the module does not see the literal: import its module (and
          `meta import` it too if the module has `meta import`s). In a
          registration file, whose proofs are the defaults, that is the fix.
          In a proof, it is only if the check is `lit_decide` or
          `taint_decide`: `decide +kernel` and `by decide` read no literal,
          and need `lit_decide` as well (measure: the time may be elsewhere).
  seen    the module sees the literal but the check did not use it: a
          `decide +kernel` that should be `lit_decide`, or code `rw_lit`
          does not find (nested in code without a literal, or written with
          other arguments than the literal's).

Measure every change as .agents/skills/lean-profiling/SKILL.md says; the
times here only rank.

  lit_imports.py [--target T ...] [-j N] [--min-kernel S]
                       [--min-literal S] [--top N] [--raw FILE]

`--min-kernel` (default 2 s) and `--min-literal` (default 0.3 s) leave out
cheap declarations and literals of cheap code. `--raw` also writes every
line `CheckLitImports.lean` printed, unweighed.
"""

import argparse
import collections
import concurrent.futures
import pathlib
import re
import subprocess
import sys
import tempfile

import lean_cache
import lean_profile

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"
ROOT_DIRS = ("Artifacts", "Generic", "Variants")
LITERAL = re.compile(r"\[line \d+\] materialize_\w+ ([\w.']+)")


def targets():
    return sorted(p.name for p in (LEAN / "VerifiedGarbage/TCB").iterdir() if p.is_dir())


def roots(target):
    """The registration files of `target`: those with a directory or file
    named after it."""
    out = []
    for d in ROOT_DIRS:
        for f in sorted((LEAN / "VerifiedGarbage" / d).rglob("*.lean")):
            parts = f.relative_to(LEAN).with_suffix("").parts
            if target in parts:
                out.append(".".join(parts))
    return out


def scan(target):
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write("\n".join(roots(target)) + "\n")
        f.flush()
        r = subprocess.run(["lake", "env", "lean", "--run", "CheckLitImports.lean", f.name],
                           cwd=LEAN, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"CheckLitImports.lean failed for {target}:\n{r.stderr}{r.stdout}")
    return [line.split("\t") for line in r.stdout.splitlines() if line.count("\t") == 6]


def parent(name):
    """The declaration the profile attributes an auxiliary proof to."""
    name = re.sub(r"^_private\.[\w.']+?\.0\.", "", name)
    return re.sub(r"\._proof_\d+(_\d+)?$", "", name)


def literal_times(rows):
    """Kernel time of each `materialize_*` command, by (module, its name)."""
    out = collections.Counter()
    for r in rows:
        m = LITERAL.match(r["decl"])
        if m:
            out[(r["module"], m.group(1))] += r["kernel"]
    return out


def literal_time(times, module, lit):
    parts = lit.split(".")
    for i in range(len(parts)):
        t = times.get((module, ".".join(parts[i:])))
        if t is not None:
            return t
    return None


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--target", action="append", choices=targets())
    parser.add_argument("-j", type=int, default=2, help="targets scanned at once (3-8 GB each)")
    parser.add_argument("--min-kernel", type=float, default=2.0)
    parser.add_argument("--min-literal", type=float, default=0.3)
    parser.add_argument("--top", type=int, default=100)
    parser.add_argument("--raw", type=pathlib.Path)
    args = parser.parse_args(argv)

    rows, _, _ = lean_profile.collect(lean_profile.BUILD, [])
    if not rows:
        sys.exit("no profile: restore the CI build cache with `unpack --logs` (lean/README.md) or build first")
    kernel = {(r["module"], r["decl"]): r["kernel"] for r in rows}
    lit_times = literal_times(rows)

    chosen = args.target or targets()
    # `CheckLitImports.lean` is not a module: it reads the private parts of all
    # it imports, which a build restored with `--empty-private` leaves empty.
    lean_cache.fill_private(LEAN, [m for t in chosen for m in roots(t)])
    with concurrent.futures.ThreadPoolExecutor(args.j) as pool:
        lines = [l for ls in pool.map(scan, chosen) for l in ls]
    if args.raw:
        args.raw.write_text("".join("\t".join(l) + "\n" for l in lines))

    found = collections.defaultdict(dict)
    for module, decl, _, _, lit_module, seen, lit in lines:
        t = literal_time(lit_times, lit_module, lit)
        found[(module, parent(decl))][(lit_module, lit, seen)] = t if t is not None else 0.0
    report = []
    for (module, decl), lits in found.items():
        k = kernel.get((module, decl), 0.0)
        lits = {l: t for l, t in lits.items() if t >= args.min_literal}
        if k >= args.min_kernel and lits:
            report.append((k, module, decl, lits))
    report.sort(key=lambda r: -r[0])

    print(f"{len(report)} declarations, {sum(r[0] for r in report):.0f} s of kernel time "
          f"(of at least {args.min_kernel} s, with literals of at least {args.min_literal} s)")
    for k, module, decl, lits in report[:args.top]:
        print(f"{k:6.1f} s  {module}  {decl}")
        for (lit_module, lit, seen), t in sorted(lits.items(), key=lambda x: -x[1]):
            print(f"           {seen:6}  {lit} ({t:.2f} s)  {lit_module}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
