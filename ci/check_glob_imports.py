#!/usr/bin/env python3
"""Checks that no hand-written Rust file has a glob import (`use a::*;`,
`use super::*;`, `use a::{b, *};`, `pub use a::*;`): every import names
what it imports. Exits non-zero naming each one.

Clippy's `wildcard_imports`, which `Cargo.toml` denies (with
`warn-on-all-wildcard-imports` in `clippy.toml`), catches them in the
library and the benchmarks, but it skips every crate built for tests
(`--test`): the library's `#[cfg(test)]` modules and `tests/`. This
checks every tracked `.rs` file but the generated crates',
`crates/verified-garbage-asm-<target>/`, which the Lean emitter writes.

    python3 ci/check_glob_imports.py
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
GENERATED = re.compile(r"^crates/verified-garbage-asm-[^/]+/")

# A `use` declaration, from `use` to its `;` (which a use tree cannot hold).
USE = re.compile(r"\buse\b([^;]*);")
# A glob in a use tree: `*` after `::`, `{` or `,`, before `,`, `}` or the
# end; but not a macro's repetition, `$(...),*`, whose `,` follows a `)`.
GLOB = re.compile(r"(?:::|\{|(?<!\)),)\s*\*\s*(?:,|\}|$)")


def strip(text: str) -> str:
    """`text` with its comments and the contents of its string and character
    literals blanked out (each character but a newline made a space), so that
    line numbers stay and nothing in them looks like code."""
    out = []
    i, n = 0, len(text)

    def blank(s: str) -> str:
        return "".join(c if c == "\n" else " " for c in s)

    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(text[i:j]))
            i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(text[i:j]))
            i = j
        elif (m := re.compile(r'b?r(#*)"').match(text, i)) and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")
        ):
            end = '"' + m.group(1)
            j = text.find(end, m.end())
            j = n if j < 0 else j + len(end)
            out.append(blank(text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(blank(text[i : j + 1]))
            i = j + 1
        elif c == "'" and (m := re.compile(r"'(?:\\.[^']*|[^\\'])'").match(text, i)):
            out.append(blank(m.group(0)))
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


def globs(text: str) -> list[int]:
    """The lines of `text`, a Rust file, where a `use` with a glob starts."""
    code = strip(text)
    return [
        code.count("\n", 0, m.start()) + 1
        for m in USE.finditer(code)
        if GLOB.search(m.group(1))
    ]


def main() -> int:
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.rs"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout.decode()
    bad = 0
    for path in sorted(p for p in out.split("\0") if p):
        if GENERATED.match(path):
            continue
        text = (ROOT / path).read_text()
        for line in globs(text):
            print(
                f"{path}:{line}: a glob import: name what it imports",
                file=sys.stderr,
            )
            bad += 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
