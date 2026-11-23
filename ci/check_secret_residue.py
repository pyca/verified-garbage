#!/usr/bin/env python3
"""Checks that the library's Rust code never moves, shortens or grows a
buffer without saying why that leaves no secret behind.

Moving bytes within a `Vec` (`drain`, `copy_within`, `remove`, ...) copies
them without clearing where they were; shortening it (`truncate`,
`set_len`) leaves the tail in the allocation; and growing it (`push`,
`extend_from_slice`, `resize`, `reserve`, ...) may reallocate, freeing the
old allocation without wiping it. Either way, a secret can stay in memory
that the caller cannot reach to wipe (#6301: RSAES-PKCS1-v1_5 decryption's
`drain`). CLAUDE.md's rule: the verified code lays out a secret result so
that the Rust code only shortens it over zeros, and the Rust code never
moves secret bytes itself.

So every call of those methods in `src/`, but in test code (`#[cfg(test)]`
items, and the files `tests.rs` and `*_tests.rs`), needs a comment

    // NO-SECRET-RESIDUE: <why>

at the end of its line, or in the comment lines just above it, saying why
it leaves no secret behind: the buffer holds only public data, its
capacity was reserved exactly before anything was written, what is left
behind is zeros by the contract of the function that wrote it, ... The
check matches method names, not types, so it also asks about a map's
`insert` or an iterator's `extend`: say so in the comment.

    python3 ci/check_secret_residue.py
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

METHODS = (
    # Moves bytes within the buffer.
    "drain copy_within rotate_left rotate_right split_off swap_remove remove insert "
    "retain retain_mut dedup dedup_by dedup_by_key splice "
    # Shortens it, leaving the tail.
    "truncate set_len "
    # Grows it, which may reallocate.
    "push extend extend_from_slice extend_from_within append resize resize_with "
    "reserve reserve_exact try_reserve try_reserve_exact shrink_to shrink_to_fit"
).split()
CALL = re.compile(r"\.(" + "|".join(METHODS) + r")\s*(?:::\s*<[^>]*>\s*)?\(")
MARKER = re.compile(r"//\s*NO-SECRET-RESIDUE:\s*\S")
CFG_TEST = re.compile(r"#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]")


def code_only(text: str) -> str:
    """`text` with its comments and the contents of its string and character
    literals replaced by spaces, keeping newlines, so that offsets and line
    numbers are unchanged."""
    out = list(text)
    i, n = 0, len(text)

    def blank(a: int, b: int) -> None:
        for j in range(a, b):
            if out[j] != "\n":
                out[j] = " "

    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
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
            blank(i, j)
            i = j
        elif m := re.match(r'b?r(#*)"', text[i:]):
            end = text.find('"' + m.group(1), i + m.end())
            j = n if end < 0 else end + 1 + len(m.group(1))
            blank(i + m.end(), j - 1 - len(m.group(1)))
            i = j
        elif c == '"' or text.startswith('b"', i):
            j = i + (2 if c == "b" else 1)
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i + 1, j)
            i = j + 1
        elif m := re.match(r"b?'(\\.[^']*|[^\\'])'", text[i:]):
            blank(i + 1, i + m.end() - 1)
            i += m.end()
        else:
            i += 1
    return "".join(out)


def test_spans(code: str) -> list[tuple[int, int]]:
    """The spans of `code` that are `#[cfg(test)]` items: from the attribute
    to the end of the item's block, or to its `;`."""
    spans = []
    for m in CFG_TEST.finditer(code):
        j = m.end()
        while j < len(code) and code[j] not in "{;":
            j += 1
        if j < len(code) and code[j] == "{":
            depth = 0
            while j < len(code):
                depth += {"{": 1, "}": -1}.get(code[j], 0)
                j += 1
                if depth == 0:
                    break
        spans.append((m.start(), j))
    return spans


def justified(lines: list[str], k: int) -> bool:
    """Whether line `k` (0-based), or the comment lines just above it, carry
    the marker."""
    if MARKER.search(lines[k]):
        return True
    k -= 1
    while k >= 0 and lines[k].lstrip().startswith("//"):
        if MARKER.search(lines[k]):
            return True
        k -= 1
    return False


def violations_in(text: str) -> list[tuple[int, str]]:
    """The unjustified calls in `text`: (line number, method)."""
    code = code_only(text)
    spans = test_spans(code)
    lines = text.split("\n")
    out = []
    for m in CALL.finditer(code):
        if any(a <= m.start() < b for a, b in spans):
            continue
        k = code.count("\n", 0, m.start())
        if not justified(lines, k):
            out.append((k + 1, m.group(1)))
    return out


def is_test_file(path: pathlib.Path) -> bool:
    return path.name == "tests.rs" or path.name.endswith("_tests.rs")


def violations(root: pathlib.Path) -> list[str]:
    out = []
    for path in sorted((root / "src").rglob("*.rs")):
        if is_test_file(path):
            continue
        rel = path.relative_to(root)
        for line, method in violations_in(path.read_text()):
            out.append(f"{rel}:{line}: `.{method}(` without a `// NO-SECRET-RESIDUE: <why>`")
    return out


def main() -> int:
    found = violations(ROOT)
    for v in found:
        print(v, file=sys.stderr)
    if found:
        print(
            "\nEach call above moves, shortens or grows a buffer, which can leave a "
            "secret in memory the caller cannot wipe. Say why it does not, in a "
            "`// NO-SECRET-RESIDUE: <why>` comment on or just above its line "
            "(ci/check_secret_residue.py), or have the verified code lay out the "
            "result so that it need not.",
            file=sys.stderr,
        )
        return 1
    print("No unjustified buffer moves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
