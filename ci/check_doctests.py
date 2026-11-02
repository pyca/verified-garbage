#!/usr/bin/env python3
"""Checks that the library's documentation has no code blocks, which
rustdoc would run as doc-tests: Cargo.toml turns them off (`[lib]
doctest = false`), since there were none and `cargo test` spent 2 s on
RISC-V compiling the crate's documentation to find that out. A code block
would never run, so this fails on one, naming it: turn doc-tests back on
with it.

A code block is a fenced one (three backticks or tildes, on any line of
`src/`, so that a `#[doc = …]` attribute's text counts too) or an indented
one (a line of a `///` or `//!` comment indented four spaces or a tab more
than the comment's own). Indentation inside a list item is not code to
rustdoc, but counts here: write such a line with less.
"""

import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent

COMMENT = re.compile(r"^\s*//[/!](?![/!])(.*)$")
FENCE = re.compile(r"```|~~~")
INDENTED = re.compile(r"^ ?( {4}|\t)\S")


def code_blocks(text: str) -> list[int]:
    """The lines of `text` (numbered from 1) that are or may start a doc
    code block."""
    found = []
    for n, line in enumerate(text.splitlines(), 1):
        m = COMMENT.match(line)
        if FENCE.search(line) or (m and INDENTED.match(m[1])):
            found.append(n)
    return found


def doctests_off(manifest: str) -> bool:
    return tomllib.loads(manifest).get("lib", {}).get("doctest") is False


def main() -> int:
    errors = []
    if not doctests_off((ROOT / "Cargo.toml").read_text()):
        print("Cargo.toml runs doc-tests: this check is only for `[lib] doctest = false`", file=sys.stderr)
        return 1
    for path in sorted((ROOT / "src").rglob("*.rs")):
        for n in code_blocks(path.read_text()):
            errors.append(f"{path.relative_to(ROOT)}:{n}: a doc code block, which would never run")
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        print("doc-tests are off (Cargo.toml's `[lib] doctest = false`): turn them back on, "
              "and delete this check, to add an example that runs", file=sys.stderr)
        return 1
    print("no doc code blocks")
    return 0


if __name__ == "__main__":
    sys.exit(main())
