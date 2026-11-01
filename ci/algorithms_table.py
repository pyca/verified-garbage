#!/usr/bin/env python3
"""Generates the tables in the Algorithms section of README.md, one per
family, from what the repository contains. Each docs/algorithms/<name>.toml
is a row:

  name     what the table calls it
  family   the table it goes in, one of FAMILIES
  specs    its Lean specs, lean/VerifiedGarbage/Spec/<spec>.lean
  modules  the Rust modules of its public API
  asm      the generated modules, crates/verified-garbage-asm-<arch>/src/<asm>.rs, whose functions
           it runs

and nothing else: a row describes no optimizations by hand.

* Spec landed: every spec exists.
* One column per architecture: ✅ if it is in the `target_arch`s of every
  module's inner `#![cfg(...)]` (so every module must exist and have one),
  followed by its variants, all read from the `asm` modules: the CPU
  features their functions need (a generated `_FEATURES` constant), and
  the variants that need none, by their suffix (`SUFFIXES`).

Every cell is on a line of its own (`tr`), so that git merges PRs that
change different cells without a conflict.

`--check` writes nothing and fails if README.md is not up to date (CI runs
it).
"""

import html
import pathlib
import re
import sys
import tomllib

import asm_layout

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
ROWS = ROOT / "docs" / "algorithms"
BEGIN = "<!-- BEGIN ci/algorithms_table.py: edit docs/algorithms/, then run it -->\n"
END = "<!-- END ci/algorithms_table.py -->\n"

# The architectures, in table order: Rust's name and the table's.
ARCHES = {
    "x86_64": "x86-64",
    "aarch64": "ARM64",
    "arm": "ARMv7",
    "x86": "x86",
    "powerpc64": "PPC64LE",
    "riscv64": "RISC-V",
}

# The crate of an architecture's generated modules, verified-garbage-asm-<dir>, where
# it is not the architecture's name (the verified code is little-endian only).
ASM_DIRS = {"powerpc64": "powerpc64le"}

# The families, in README order: each has its own table, under a heading.
FAMILIES = ["Hashes", "MACs", "Ciphers", "AEADs", "KDFs", "KEMs", "Key agreement", "Signatures", "DSA", "RSA"]

# How the table names CPU features (Rust's `target_feature` names), in the
# order it lists them; None leaves a feature out, e.g. one that only comes
# with another.
FEATURES = {
    "sha": "SHA extensions",
    "sha512": "SHA512",
    "aes": "AES-NI",
    "vaes": "VAES",
    "pclmulqdq": "PCLMULQDQ",
    "vpclmulqdq": "VPCLMULQDQ",
    "ssse3": "SSSE3",
    "avx512f": "AVX-512F",
    "avx512ifma": "AVX-512 IFMA",
    "avx512vl": "AVX-512VL",
    "avx512bw": "AVX-512BW",
    "avx2": "AVX2",
    "avx": "AVX",
    "bmi1": "BMI1",
    "bmi2": "BMI2",
    "adx": "ADX",
    "sve2": "SVE2",
}

# Features that come with others: every CPU with the key's has the value's
# (AVX2 is an extension of AVX; SSSE3 predates the rest). A cell leaves out
# a feature that another of its features brings.
IMPLIES = {"avx2": {"avx"}, "avx": {"ssse3"}, "aes": {"ssse3"}, "pclmulqdq": {"ssse3"}, "sha": {"ssse3"}}

# The variants that need no CPU feature beyond the architecture's baseline,
# so have no `_FEATURES` constant, by architecture: the suffix of the
# function's name and how the table names it.
SUFFIXES = {"aarch64": {"neon": "NEON"}}

# The keys of a row.
KEYS = {"name", "family", "specs", "modules", "asm"}

# Names that differ on one architecture: AArch64's `aes` (Rust's name for
# FEAT_AES with FEAT_PMULL) is not AES-NI.
ARCH_FEATURES = {"aarch64": {"aes": "AES, PMULL", "sha2": "SHA extensions", "sha3": "SHA extensions"}}

CFG = re.compile(r"^#!\[cfg\((.*?)\)\]$", re.MULTILINE | re.DOTALL)
ARCH = re.compile(r'target_arch\s*=\s*"(\w+)"')
# A generated `_FEATURES` constant: the bits of its features, by name in uppercase.
# (`crate::cpu::` in a crate whose `cpu` is `verified_garbage_cpu`, or that
# crate's name.)
FEATURE_CONST = re.compile(
    r"_FEATURES: (?:crate::cpu|verified_garbage_cpu)::Features = (?:crate::cpu|verified_garbage_cpu)::Features\((.*?)\);")
FEATURE_BIT = re.compile(r"(?:crate::cpu|verified_garbage_cpu)::feature::(\w+)")
FUNCTION = re.compile(r"\bfn (vg_\w+)\(")


def supported(row, errors):
    names = set(ARCHES)
    for module in row["modules"]:
        path = ROOT / module
        if not path.is_file():
            return set()
        cfg = CFG.search(path.read_text())
        if not cfg:
            errors.append(f"{module}: no inner #![cfg(...)] naming its architectures")
            return set()
        names &= set(ARCH.findall(cfg[1]))
    return names


def implied(features):
    """The features that others of `features` imply, directly or not."""
    out, todo = set(), [g for f in features for g in IMPLIES.get(f, ())]
    while todo:
        f = todo.pop()
        if f not in out:
            out.add(f)
            todo += IMPLIES.get(f, ())
    return out


def variants(row, arch):
    """How `row`'s variants on `arch` are named: the CPU features they need,
    then the variants that need none."""
    features, suffixes = set(), SUFFIXES.get(arch, {})
    found = set()
    for asm in row["asm"]:
        path = asm_layout.target_dir(ROOT, ASM_DIRS.get(arch, arch)) / f"{asm}.rs"
        if path.is_file():
            text = path.read_text()
            for m in FEATURE_CONST.finditer(text):
                features |= {f.lower() for f in FEATURE_BIT.findall(m[1])}
            found |= {s for f in FUNCTION.findall(text) for s in suffixes if f.endswith(f"_{s}")}
    features -= implied(features)
    order = list(FEATURES)
    shown = []
    for f in sorted(features, key=lambda f: (order.index(f) if f in order else len(order), f)):
        f = {**FEATURES, **ARCH_FEATURES.get(arch, {})}.get(f, f)
        # Several features may share a name (AArch64's SHA-2 and SHA-3).
        if f is not None and f not in shown:
            shown.append(f)
    return ", ".join(shown + [suffixes[s] for s in suffixes if s in found])


def cell(text):
    """A cell's HTML: `code` spans become <code>, the rest is escaped."""
    parts = html.escape(text, quote=False).split("`")
    return "".join(f"<code>{p}</code>" if i % 2 else p for i, p in enumerate(parts))


def tr(tag, cells):
    """A table row, with every cell on its own line between blank lines."""
    return "<tr>\n\n" + "".join(f"<{tag}>{c}</{tag}>\n\n" for c in cells) + "</tr>\n\n"


def table(errors):
    header = tr("th", ["Algorithm", "Spec landed", *ARCHES.values()])
    families = {f: [] for f in FAMILIES}
    for path in sorted(ROWS.glob("*.toml")):
        row = tomllib.loads(path.read_text())
        missing = [k for k in ("name", "family", "specs", "modules", "asm") if k not in row]
        if missing:
            errors.append(f"{path.relative_to(ROOT)}: missing {', '.join(missing)}")
            continue
        if row["family"] not in families:
            errors.append(f"{path.relative_to(ROOT)}: family must be one of {', '.join(FAMILIES)}")
            continue
        unknown = set(row) - KEYS
        if unknown:
            errors.append(f"{path.relative_to(ROOT)}: unknown keys {', '.join(sorted(unknown))}; the table "
                          "names only what the code states, the CPU features and suffixes of its variants")
            continue
        spec = all((ROOT / "lean/VerifiedGarbage/Spec" / f"{s}.lean").is_file() for s in row["specs"])
        names = supported(row, errors)
        cells = [row["name"], "✅" if spec else "❌"]
        for arch in ARCHES:
            opt = variants(row, arch) if arch in names else ""
            cells.append(("✅" if arch in names else "❌") + (f" {opt}" if opt else ""))
        families[row["family"]].append(tr("td", [cell(c) for c in cells]))
    return "\n".join(
        f"### {f}\n\n<table>\n\n{header}{''.join(rows)}</table>\n" for f, rows in families.items() if rows
    )


def main() -> int:
    check = sys.argv[1:] == ["--check"]
    errors = []
    text = README.read_text()
    if BEGIN not in text or END not in text:
        errors.append(f"README.md: no {BEGIN.strip()} ... {END.strip()} section")
    else:
        head, rest = text.split(BEGIN, 1)
        _, tail = rest.split(END, 1)
        new = head + BEGIN + "\n" + table(errors) + "\n" + END + tail
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    if new == text:
        print("README.md algorithm table OK")
        return 0
    if check:
        print("README.md's algorithm table is out of date: run python3 ci/algorithms_table.py", file=sys.stderr)
        return 1
    README.write_text(new)
    print("wrote README.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
