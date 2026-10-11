#!/usr/bin/env python3
"""Converts Lean files to modules of Lean's module system, keeping what
every importer sees.

  modularize.py PATH...   convert each `.lean` file at PATH (a file or a
                          directory, recursively) that is not a module yet
  modularize.py check LOG
                          fail if a `lake build` log (LOG, `-` for stdin)
                          shows an exposed declaration referring to a
                          private one of its module, listing each

A converted file starts with `module`; its imports become `public import`
(a module may import only modules, so a layer is converted only once what it
imports is); and its body is an `@[expose] public section`, so that every
declaration stays visible to importers with its definition, as before.

A file that only defines tactics, elaborators or commands (it imports `Lean`
and declares `elab`, `syntax`, `macro` or `simproc`s, and no theorem) is
meta code: it imports `Lean` as `public meta import` and its body is a
`public meta section`, so that its definitions run at elaboration time in
the files that use them.

An exposed declaration may not refer to a private one of its module (Lean:
"A private declaration `x` (from the current module) exists but would need
to be public to access here"). The conversion does not change visibility:
`check` lists such declarations from a build of the layer, which become
public (or are renamed, if that would clash) in a small PR of their own
before the layer is converted.

The conversion is mechanical and idempotent: rerun it on a layer after
merging, rather than editing headers by hand.
"""

import pathlib
import re
import sys

IMPORT = re.compile(r"^import\s+(\S+)\s*$")
META_DECL = re.compile(r"^(elab|syntax|macro|macro_rules|simproc|dsimproc|elab_rules)\b", re.M)
THEOREM = re.compile(r"^(@\[[^\]]*\]\s*)?(private\s+)?(theorem|lemma)\b", re.M)


def is_module(lines: list[str]) -> bool:
    for l in lines:
        s = l.strip()
        if s == "module":
            return True
        if s and not s.startswith("--"):
            return False
    return False


def is_meta(text: str, imports: list[str]) -> bool:
    return (any(i == "Lean" or i.startswith("Lean.") for i in imports)
            and META_DECL.search(text) is not None and THEOREM.search(text) is None)


def convert(text: str) -> str:
    lines = text.split("\n")
    if is_module(lines):
        return text
    i, n, head = 0, len(lines), []
    while i < n and (IMPORT.match(lines[i]) or lines[i].strip() == "" or lines[i].startswith("--")):
        head.append(lines[i])
        i += 1
    imports = [IMPORT.match(l).group(1) for l in head if IMPORT.match(l)]
    meta = is_meta(text, imports)
    out = ["module", ""]
    for l in head:
        m = IMPORT.match(l)
        if m:
            core = m.group(1) == "Lean" or m.group(1).startswith("Lean.")
            l = f"public {'meta ' if meta and core else ''}import {m.group(1)}"
        out.append(l)
    while out and out[-1].strip() == "":
        out.pop()
    out.append("")
    # The module's docstring stays right after the imports.
    if i < n and lines[i].startswith("/-!"):
        while i < n:
            out.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
        out.append("")
    out.append("public meta section" if meta else "@[expose] public section")
    out.append("")
    while i < n and lines[i].strip() == "":
        i += 1
    out += lines[i:]
    return "\n".join(out)


PRIVATE_NEEDED = re.compile(
    r"^(?:error: )?(\S+\.lean):\d+:\d+: (?:error[^\n:]*: )?Unknown identifier `([^`]+)`\s*\n\s*\n?"
    r"Note: A private declaration `([^`]+)` \(from the current module\) exists", re.M)


def needs_public(log: str) -> list[tuple[str, str]]:
    """The (file, declaration) pairs of private declarations a build log
    shows exposed declarations referring to."""
    return sorted({(m.group(1), m.group(3)) for m in PRIVATE_NEEDED.finditer(log)})


def main(args: list[str]) -> int:
    if len(args) == 2 and args[0] == "check":
        log = sys.stdin.read() if args[1] == "-" else pathlib.Path(args[1]).read_text()
        found = needs_public(log)
        for f, name in found:
            print(f"{f}: private `{name}` is referred to by an exposed declaration", file=sys.stderr)
        return 1 if found else 0
    if not args:
        print(__doc__, file=sys.stderr)
        return 2
    files = []
    for a in args:
        p = pathlib.Path(a)
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    changed = 0
    for f in files:
        text = f.read_text()
        new = convert(text)
        if new != text:
            f.write_text(new)
            changed += 1
    print(f"{changed} of {len(files)} files converted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
