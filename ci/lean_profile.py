#!/usr/bin/env python3
"""Lists the declarations that cost the Lean build the most, from the build
itself: no profiling run.

Every module is built with Lean's `profiler` on (`lean/lakefile.toml`), which
reports each step over `profiler.threshold` (1 ms) as a message at the
declaration it belongs to (`type checking took 609ms`, `simp took 890ms`).
Lake keeps a module's messages in its `.trace` file, next to its `.olean`,
and the CI build cache (`lean/README.md`) ships those files: after restoring
the cache, this reads the profile of every module CI built, attributing each
step to the declaration whose source range (from the module's `.ilean`, of
the same build) contains it. A step outside every declaration (a command
that generates declarations, such as `materialize_code`, `taint_summary` or
`run_cmd`, which has no range) is grouped by its command's line, labelled
with the start of that line of the source file, if it exists:
`[line 70] taint_summary winBuildSum : taintS τB winBuild`.

Each declaration's time is split into:

  kernel   the kernel checking it (`type checking`): what `decide +kernel`,
           `taint_decide`, `lit_decide` and large proof terms cost
  elab     everything else Lean did for it: tactics, `simp`, `omega`,
           instances, compilation, linting
  blocked  time its task waited for another (with `Elab.async`, the build's
           default, e.g. for the kernel to check a lemma it uses); not work
           of its own, and not counted in `total`

Times are wall-clock times of one build on one CI runner: rank by them, but
measure a change as CLAUDE.md ("Keeping proofs fast") says, not by them.

  lean_profile.py [--top N] [--sort kernel|elab|total] [--by decl|module]
                  [--module PREFIX ...] [--tests] [--json] [--build DIR]
                  [--source DIR]

`--module` keeps the modules whose names start with any PREFIX
(`VerifiedGarbage.Proof.Sha256`). `--by module` sums each module's
declarations instead. The known-answer tests (`VerifiedGarbageTest`), whose
cost is evaluating specs rather than checking proofs, are left out (their
total is printed) unless `--tests` is given or a PREFIX names them. `--json`
prints every row, sorted, with no limit: a row outside declarations has a
`line` as well as its label in `decl`; a `--by module` row has no `decl`.
"""

import argparse
import json
import pathlib
import re
import sys

SOURCE = pathlib.Path(__file__).resolve().parent.parent / "lean"
BUILD = SOURCE / ".lake/build/lib/lean"
TESTS = "VerifiedGarbageTest"
# How much of a source line labels a step outside declarations.
LABEL_WIDTH = 80
KINDS = ("kernel", "elab", "blocked")
# A stored message: `<file>:<line>:<column>: <text>`, the text one step per
# line (`<what> took <n>ms`).
MESSAGE = re.compile(r"^(.+?):(\d+):(\d+): (.*)$", re.S)
TOOK = re.compile(r"^(.*) took ([0-9.]+)(ms|s)$")


def kind(what):
    if what == "type checking":
        return "kernel"
    if what.startswith("blocked"):
        return "blocked"
    return "elab"


def steps(log):
    """The profiled steps of a module's stored build log: (line, column,
    kind, seconds), with Lean's 1-based lines and 0-based columns. Lean
    reports some messages twice (of commands that make it generate
    definitions, such as equation lemmas): each is counted once."""
    seen = set()
    for entry in log:
        if entry.get("level") != "info" or entry.get("message") in seen:
            continue
        seen.add(entry.get("message"))
        m = MESSAGE.match(entry.get("message", ""))
        if not m:
            continue
        line, col = int(m.group(2)), int(m.group(3))
        for text in m.group(4).splitlines():
            t = TOOK.match(text.strip())
            if t:
                secs = float(t.group(2)) / (1000 if t.group(3) == "ms" else 1)
                yield line, col, kind(t.group(1)), secs


def declaration(decls, line, col):
    """The innermost declaration whose range contains Lean's position
    (`line` 1-based) in `decls`, an `.ilean`'s `decls` (0-based lines),
    with its doc comment and attributes."""
    pos, best, size = (line - 1, col), None, None
    for name, r in decls.items():
        start, end = (r[0], r[1]), (r[2], r[3])
        if start <= pos <= end:
            s = (r[2] - r[0], r[3] - r[1])
            if size is None or s < size:
                best, size = name, s
    return best


def module_profile(trace, ilean):
    """Seconds per kind for each declaration of one module, from its
    `.trace` (JSON) and a function reading its `.ilean` (JSON), called only
    if the module has a profile. Steps outside every declaration (`open`,
    `set_option`, commands such as `#eval` or `taint_summary`) are counted
    under their line (an `int`), declarations under their name."""
    found_steps = list(steps(trace.get("log", [])))
    if not found_steps:
        return {}
    decls = ilean().get("decls", {})
    out, found = {}, {}
    for line, col, k, secs in found_steps:
        # A message's steps share its position.
        if (line, col) not in found:
            found[line, col] = declaration(decls, line, col) or line
        d = out.setdefault(found[line, col], dict.fromkeys(KINDS, 0.0))
        d[k] += secs
    return out


def module_name(path, build):
    return ".".join(path.relative_to(build).with_suffix("").parts)


def is_test(mod):
    return mod.split(".")[0] == TESTS


def source_lines(source, mod):
    """The lines of a module's source file under `source`, or `None`."""
    path = source / pathlib.Path(*mod.split(".")).with_suffix(".lean")
    try:
        return path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None


def line_label(lines, line):
    """`[line N]` and the start of Lean's 1-based `line` of `lines`."""
    label = f"[line {line}]"
    text = lines[line - 1].strip() if lines and 0 < line <= len(lines) else ""
    if len(text) > LABEL_WIDTH:
        text = text[:LABEL_WIDTH - 1] + "…"
    return f"{label} {text}" if text else label


def collect(build, prefixes, source=SOURCE, tests=False):
    """Rows (module, declaration or line, seconds per kind) of every built
    module under `build` whose name starts with a prefix, the count of
    modules whose logs held no profile, and the count and seconds of the
    test modules left out (all of them unless `tests` or a prefix names
    them)."""
    tests = tests or any(is_test(p) for p in prefixes)
    rows, unprofiled, skipped = [], 0, [0, 0.0]
    for trace_path in sorted(build.rglob("*.trace")):
        mod = module_name(trace_path, build)
        if prefixes and not mod.startswith(tuple(prefixes)):
            continue
        ilean_path = trace_path.with_suffix(".ilean")
        if not ilean_path.exists():
            continue
        prof = module_profile(json.loads(trace_path.read_text()),
                              lambda: json.loads(ilean_path.read_text()))
        if not prof:
            unprofiled += 1
        if is_test(mod) and not tests:
            if prof:
                skipped[0] += 1
                skipped[1] += sum(map(total, prof.values()))
            continue
        lines = None
        for decl, secs in prof.items():
            if isinstance(decl, int):
                if lines is None:
                    lines = source_lines(source, mod) or []
                rows.append({"module": mod, "decl": line_label(lines, decl),
                             "line": decl, **secs})
            else:
                rows.append({"module": mod, "decl": decl, **secs})
    return rows, unprofiled, tuple(skipped)


def by_module(rows):
    mods = {}
    for r in rows:
        m = mods.setdefault(r["module"], {"module": r["module"],
                                          **dict.fromkeys(KINDS, 0.0)})
        for k in KINDS:
            m[k] += r[k]
    return list(mods.values())


def total(row):
    return row["kernel"] + row["elab"]


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--sort", choices=("kernel", "elab", "total"), default="total")
    parser.add_argument("--by", choices=("decl", "module"), default="decl")
    parser.add_argument("--module", action="append", default=[], metavar="PREFIX")
    parser.add_argument("--tests", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--build", type=pathlib.Path, default=BUILD)
    parser.add_argument("--source", type=pathlib.Path, default=SOURCE)
    args = parser.parse_args(argv)

    rows, unprofiled, (skipped, skipped_secs) = collect(
        args.build, args.module, args.source, args.tests)
    if not rows:
        sys.exit(f"no profiles under {args.build}: restore the CI cache, or build "
                 "with the lakefile's `profiler` options")
    if args.by == "module":
        rows = by_module(rows)
    key = total if args.sort == "total" else (lambda r: r[args.sort])
    rows.sort(key=lambda r: (-key(r), r["module"], r.get("line", 0), r.get("decl", "")))
    if skipped:
        print(f"({skipped} test modules left out, {skipped_secs:.2f}s in all: "
              f"--tests or --module {TESTS} lists them)", file=sys.stderr)
    if args.json:
        json.dump(rows, sys.stdout, indent=1)
        print()
        return
    print(f"{'total':>8} {'kernel':>8} {'elab':>8} {'blocked':>8}  "
          + ("module" if args.by == "module" else "declaration (module)"))
    for r in rows[:args.top]:
        what = r["module"] if args.by == "module" else f"{r['decl']} ({r['module']})"
        print(f"{total(r):8.2f} {r['kernel']:8.2f} {r['elab']:8.2f} "
              f"{r['blocked']:8.2f}  {what}")
    if unprofiled:
        print(f"({unprofiled} modules' logs held no profile: built before the "
              "profiler was on, or with every step under its threshold)",
              file=sys.stderr)


if __name__ == "__main__":
    main()
