#!/usr/bin/env python3
"""Checks that each target's pre-assembled code is its printed code.

The emitter prints each target's verified functions as assembly into
`crates/verified-garbage-asm-<target>/asm/`; the crate that is compiled, its
`src/`, holds them with most of their machine code as data directives
(`ci/preassemble.py`, which is not trusted). This checks, for each target,
that the two are the same code:

* every file of `src/` is its file of `asm/` but for the bodies of its
  `naked_asm!`s, and no file is in one only;
* compiling each, their object files have the same sections (each's name,
  type, flags, alignment, entry size and bytes, and its relocations: their
  offset, type, addend and the symbol they name) and the same symbols (each's
  name, value, size, type, binding, visibility and the section it is in).

Names are compared without the crate's hash (`Cs…_`), which depends on where
the crate is compiled from, and objects as one set of sections and symbols,
as the functions may be split among them differently.

A crate that is not pre-assembled compiles the emitter's output itself: its
`asm/` (ARM's, see `ci/preassemble.py`) or, where the printer already emits
the machine code, its `src/` (RISC-V's and AArch64's). It must not have both: a `src/`
beside an `asm/` would be compiled unchecked.

    python3 ci/check_preassembled.py [TARGET ...]
    python3 ci/check_preassembled.py --triples  # the Rust targets it compiles for
"""

import collections
import os
import pathlib
import re
import subprocess
import sys
import tempfile

import objfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CRATES = ROOT / "crates"
CPU_CRATE = CRATES / "verified-garbage-cpu"
PREFIX = "verified-garbage-asm-"

# The targets whose `src/` is pre-assembled, each with the triple it is
# compared for.
TRIPLES = {
    "x86_64": "x86_64-unknown-linux-gnu",
    "x86": "i686-unknown-linux-gnu",
    "powerpc64le": "powerpc64le-unknown-linux-gnu",
}

NAKED = re.compile(r"^    core::arch::naked_asm!\(\n.*?^    \)\n", re.M | re.S)
CRATE_HASH = re.compile(r"Cs[0-9A-Za-z]*_")

# Sections that describe the others, compared through them.
SHT_NULL, SHT_SYMTAB, SHT_STRTAB, SHT_RELA, SHT_REL, SHT_GROUP = 0, 2, 3, 4, 9, 17
STT_SECTION, STT_FILE = 3, 4
SHN_UNDEF, SHN_LORESERVE = 0, 0xFF00


def sources(d):
    return {p.relative_to(d).as_posix(): p.read_text() for p in sorted(d.rglob("*.rs"))}


def check_text(asm, src, target, errors):
    """`src` is `asm` (each `{path: text}`) but for the `naked_asm!` bodies."""
    for rel in sorted(set(asm) | set(src)):
        if rel not in asm or rel not in src:
            errors.append(f"{target}: {rel} is in {'src' if rel in src else 'asm'}/ only")
        elif NAKED.sub("<code>\n", asm[rel]) != NAKED.sub("<code>\n", src[rel]):
            errors.append(f"{target}: src/{rel} differs from asm/{rel} outside its code")


def build(lib, target, triple, workdir):
    """The object files of the crate whose root is `lib`, compiled for `triple`."""
    name = PREFIX + target
    (workdir / "Cargo.toml").write_text(f"""[package]
name = "{name}"
version = "0.0.0"
edition = "2024"
publish = false

[lib]
path = "{lib.as_posix()}"

[dependencies]
verified-garbage-cpu = {{ path = "{CPU_CRATE.as_posix()}" }}

[workspace]
""")
    env = dict(os.environ, CARGO_TARGET_DIR=str(workdir / "target"), CARGO_INCREMENTAL="0",
               CARGO_PROFILE_DEV_DEBUG="0")
    for v in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET"):
        env.pop(v, None)
    subprocess.run(["cargo", "build", "--lib", "-q", "--target", triple,
                    "--manifest-path", str(workdir / "Cargo.toml")], check=True, env=env)
    rlib, = (workdir / "target" / triple / "debug" / "deps").glob(f"lib{name.replace('-', '_')}-*.rlib")
    return [objfile.Elf(b) for n, b in objfile.ar_members(rlib.read_bytes()).items() if n.endswith(".o")]


def plain(name):
    return CRATE_HASH.sub("", name)


def symbol_key(o, index):
    """The symbol `index` of `o` as a relocation names it: a section's
    symbol by its section's name, any other by its name."""
    s = o.symbols[index]
    if s.type == STT_SECTION:
        return "section " + plain(o.sections[s.shndx].name)
    return plain(s.name)


def section_of(o, s):
    if s.shndx == SHN_UNDEF:
        return None
    if s.shndx >= SHN_LORESERVE:  # ABS, COMMON
        return s.shndx
    return plain(o.sections[s.shndx].name)


def contents(objects):
    """What `check_objects` compares of `objects`: a count of each of their
    sections and of each of their defined symbols."""
    sections, symbols = collections.Counter(), collections.Counter()
    for o in objects:
        for sec in o.sections:
            if sec.type in (SHT_NULL, SHT_SYMTAB, SHT_STRTAB, SHT_RELA, SHT_REL):
                continue
            data = sec.data
            if sec.type == SHT_GROUP:  # its flags, then its members, by name
                words = [int.from_bytes(data[i:i + 4], "little") for i in range(0, len(data), 4)]
                data = (words[0], plain(o.symbols[sec.info].name),
                        tuple(sorted(plain(o.sections[i].name) for i in words[1:])))
            relocs = tuple(sorted((r.offset, r.type, r.addend, symbol_key(o, r.symbol))
                                  for r in o.relocs.get(sec.index, [])))
            sections[(plain(sec.name), sec.type, sec.flags, sec.align, sec.entsize, data,
                      relocs)] += 1
        for s in o.symbols:
            if s.shndx == SHN_UNDEF or s.type in (STT_SECTION, STT_FILE):
                continue
            symbols[(plain(s.name), s.value, s.size, s.info, s.other, section_of(o, s))] += 1
    return sections, symbols


def differences(triple, printed, shipped):
    """What differs between the `contents` of compiling `asm/` (`printed`)
    and `src/` (`shipped`): each section and symbol, by name, that is not
    the same in both."""
    out = []
    for what, a, s in (("section", printed[0], shipped[0]), ("symbol", printed[1], shipped[1])):
        for key in sorted(set(a) | set(s), key=repr):
            if a[key] != s[key]:
                out.append(f"{triple}: the {what} {key[0]} differs between asm/ and src/")
    return list(dict.fromkeys(out))


def check_objects(target, triple, errors, workdir):
    d = CRATES / (PREFIX + target)
    (workdir / "asm").mkdir()
    (workdir / "src").mkdir()
    printed = contents(build(d / "asm" / "lib.rs", target, triple, workdir / "asm"))
    shipped = contents(build(d / "src" / "lib.rs", target, triple, workdir / "src"))
    errors += differences(triple, printed, shipped)
    return sum(printed[1].values())


def unassembled(crates):
    """The crates of generated code under `crates` that are not
    pre-assembled but have both an `asm/` and a `src/`."""
    return [d.name for d in sorted(crates.glob(PREFIX + "*"))
            if d.name[len(PREFIX):] not in TRIPLES and (d / "asm").exists() and (d / "src").exists()]


def main(argv):
    if argv == ["--triples"]:
        print(",".join(TRIPLES.values()))
        return 0
    targets = argv or list(TRIPLES)
    errors = [f"{n}: not pre-assembled, so it compiles the emitter's asm/ or src/, not both"
              for n in unassembled(CRATES)]
    for target in targets:
        d = CRATES / (PREFIX + target)
        if not (d / "asm").is_dir():
            errors.append(f"{target}: no asm/")
            continue
        check_text(sources(d / "asm"), sources(d / "src"), target, errors)
        with tempfile.TemporaryDirectory() as w:
            n = check_objects(target, TRIPLES[target], errors, pathlib.Path(w))
        print(f"{TRIPLES[target]}: compared {n} symbols", file=sys.stderr)
    for e in errors[:50]:
        print(e, file=sys.stderr)
    if errors:
        print(f"{len(errors)} differences: run `python3 ci/preassemble.py`", file=sys.stderr)
        return 1
    print("the pre-assembled code of every target is its printed code")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
