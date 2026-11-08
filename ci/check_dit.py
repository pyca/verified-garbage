#!/usr/bin/env python3
"""Checks that each Rust module of the library decides about data independent
timing (`src/dit.rs`) as its algorithms' family requires.

Every generated dispatcher, through which alone the library calls verified
code, takes a `Dit` token. An operation that may process secrets makes it
with `dit::enter!`, which turns the mode on; one whose
inputs and outputs are all public makes it with `dit::public(Why::…)`, or
`dit::enter_if!(…, Why::…)` for a type that is either, which names why. This
checks the reasons each file gives against the families of its algorithms
(`docs/algorithms/*.toml`: `family`, and the files in `modules`):

* `Why::UnkeyedHash`: only hashes;
* `Why::Verify`: only signatures (`Signatures`, `DSA`, `RSA`);
* `Why::PublicKey`: only signatures, key agreement and KEMs;
* `Why::Wipe`: anywhere (wiping stores zeros whatever the data);
* `Why::Test`: only tests (`cfg(test)`, which the compiler checks).

So a MAC, AEAD, cipher or KDF never runs as public work, and a new
primitive gets the mode its family needs. A file that no `modules` lists
takes the families of the files listed in its directory under `src/`, or,
for `src/<name>_common.rs`, those of `src/<name>*.rs`; a file with no family
may give only `Wipe`. And only `src/dit.rs` makes tokens from nothing
(`Dit::assume`).

The tests check the rest at run time (debug builds with `cfg(test)` or the
`cpu-features-env` feature): no guard is entered inside another, and no
public token is made inside an operation that holds the mode, so each
operation decides once and passes its token down.

    python3 ci/check_dit.py
"""

import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The families that may give each reason (None: any file).
ALLOWED = {
    "UnkeyedHash": {"Hashes"},
    "Verify": {"Signatures", "DSA", "RSA"},
    "PublicKey": {"Signatures", "Key agreement", "KEMs"},
    "Wipe": None,
    "Test": None,
}

WHY = re.compile(r"\bWhy::(\w+)")
ASSUME = re.compile(r"\bDit::assume\b")
# Comments, which may name a reason in prose.
COMMENT = re.compile(r"//[^\n]*")


def families(root: pathlib.Path) -> dict[str, set[str]]:
    """Each file the `modules` of `docs/algorithms/*.toml` list, with the
    families of the algorithms that list it."""
    out: dict[str, set[str]] = {}
    for toml in sorted((root / "docs" / "algorithms").glob("*.toml")):
        data = tomllib.loads(toml.read_text())
        for module in data.get("modules", []):
            out.setdefault(module, set()).add(data["family"])
    return out


def file_families(path: str, listed: dict[str, set[str]]) -> set[str]:
    """The families of the file `path` (relative to the root, `/`-separated)."""
    if path in listed:
        return listed[path]
    parent, _, name = path.rpartition("/")
    if parent != "src":
        return set().union(*(f for m, f in listed.items() if m.rpartition("/")[0] == parent))
    if name.endswith("_common.rs"):
        stem = "src/" + name.removesuffix("_common.rs")
        return set().union(*(f for m, f in listed.items()
                             if m.startswith(stem) and m.count("/") == 1))
    return set()


def violations(root: pathlib.Path) -> list[str]:
    listed = families(root)
    errors = []
    for file in sorted((root / "src").rglob("*.rs")):
        path = file.relative_to(root).as_posix()
        text = COMMENT.sub("", file.read_text())
        if path == "src/dit.rs":
            continue
        for m in ASSUME.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            errors.append(f"{path}:{line}: only src/dit.rs makes tokens (`Dit::assume`)")
        fams = None
        for m in WHY.finditer(text):
            why = m.group(1)
            line = text.count("\n", 0, m.start()) + 1
            if why not in ALLOWED:
                errors.append(f"{path}:{line}: unknown reason `Why::{why}`")
                continue
            allowed = ALLOWED[why]
            if allowed is None:
                continue
            if fams is None:
                fams = file_families(path, listed)
            if not fams:
                errors.append(f"{path}:{line}: `Why::{why}` in a file of no algorithm's family"
                              " (docs/algorithms/*.toml `modules`)")
            elif not fams <= allowed:
                errors.append(
                    f"{path}:{line}: `Why::{why}` in a file of {', '.join(sorted(fams))}, which"
                    f" may not run as public work (only {', '.join(sorted(allowed))} may):"
                    " use `dit::enter!`")
    return errors


def main() -> int:
    errors = violations(ROOT)
    for e in errors:
        print(e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
