#!/usr/bin/env python3
"""Pre-assembles the generated code of each target.

The emitter (`lean/Emit.lean`) prints each target's verified functions as
assembly text into `crates/verified-garbage-asm-<target>/asm/`, which is
what is reviewed. Assembling 40 MB of text took most of the time it took to
compile the library, so the crate that is compiled, its `src/`, holds the
same functions with their machine code instead, as data directives,
written by this script:

* it compiles the text, with a label before each line that it keeps as
  text and after each that has a relocation;
* it keeps as text each line that names a symbol (an operand, `{name}`, or
  a page of one, `vg_sym_page!`: calls and the addresses of tables, whose
  bytes the linker writes), each alignment (which also aligns the section),
  and each label one of those names (`2b`);
* every other run of bytes between them it writes as data, `.octa`: the
  targets it pre-assembles have no mapping symbols, which data directives
  would change.

Everything else of each file (documentation, signatures, constants) is
copied as it is. This script is not trusted: `ci/check_preassembled.py`
checks that compiling `src/` gives each function the same bytes,
relocations and symbols as compiling `asm/`.

The other crates compile the emitter's output itself, and are not
pre-assembled: ARM's (`asm/`), which is built both as ARM and as Thumb code,
whose bytes differ, and which Rust cannot tell apart at compile time; and
RISC-V's, AArch64's, PPC64LE's and x86's (`src/`), whose printers already
emit each instruction's machine code (`lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`).

    python3 ci/preassemble.py [TARGET ...]          # rewrite src/
    python3 ci/preassemble.py --check [TARGET ...]  # fail if src/ is stale
"""

import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

import objfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CRATES = ROOT / "crates"
CPU_CRATE = CRATES / "verified-garbage-cpu"

# The targets pre-assembled, each with the triple whose code `src/` holds
# (an ELF one: the code is the same on every OS of the target).
TRIPLES = {
    "x86_64": "x86_64-unknown-linux-gnu",
}

NAKED = re.compile(r"^    core::arch::naked_asm!\(\n(.*?)^    \)\n", re.M | re.S)
PLACEHOLDER = re.compile(r"(?<!\{)\{[A-Za-z_]\w*\}")
LABEL_DEF = re.compile(r"^(\d+):$")
ALIGN = re.compile(r"^\.(p2align|balign|align)\b")
LABEL_REF = re.compile(r"(?<![\w#.$])(\d+)([bf])\b")


def crate_dir(target):
    return CRATES / f"verified-garbage-asm-{target}"


# --- Parsing a `naked_asm!` -------------------------------------------------

def unescape(s):
    """The value of the body of an ordinary Rust string literal, as the
    printer writes them (`\\\\`, `\\"`, `\\n`, `\\r`)."""
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == "\\":
            n = s[i + 1]
            out.append({"\\": "\\", '"': '"', "n": "\n", "r": "\r"}[n])
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def literal(s):
    """`s` as a Rust string literal (raw, unless it cannot be)."""
    if '"' not in s and "\r" not in s:
        return f'r"{s}"'
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r") + '"'


def parse_args(body):
    """The template lines and the operand lines of a `naked_asm!` body:
    `([("text" | "concat", str)], [str])`."""
    lines, operands = [], []
    rows = body.split("\n")
    i = 0
    while i < len(rows):
        row = rows[i]
        if not row.strip():
            i += 1
            continue
        s = row[8:] if row.startswith("        ") else row.strip()
        if s.startswith('r"'):
            # A raw literal, possibly over many lines, ending `",`.
            chunk = [s[2:]]
            while not chunk[-1].endswith('",'):
                i += 1
                chunk.append(rows[i])
            text = "\n".join(chunk)[:-2]
            lines += [("text", t) for t in text.split("\n")]
        elif s.startswith('"'):
            assert s.endswith('",'), s
            lines += [("text", t) for t in unescape(s[1:-2]).split("\n")]
        elif s.startswith("concat!("):
            assert s.endswith(","), s
            lines.append(("concat", s[:-1]))
        elif " = sym " in s or s.startswith("options("):
            assert s.endswith(","), s
            operands.append(s[:-1])
        else:
            raise ValueError(f"unexpected naked_asm! argument: {s!r}")
        i += 1
    return lines, operands


def kept_lines(lines):
    """The indices of the lines kept as text: each that names a symbol or
    aligns the code (`reloc`: the assembler writes their bytes, and an
    alignment also aligns the function's section), and each label
    definition one of those refers to."""
    reloc = {i for i, (kind, t) in enumerate(lines)
             if kind == "concat" or PLACEHOLDER.search(t) or ALIGN.match(t.strip())}
    labels = set()
    for i in reloc:
        for n, d in LABEL_REF.findall(lines[i][1]):
            rng = range(i - 1, -1, -1) if d == "b" else range(i + 1, len(lines))
            for j in rng:
                m = LABEL_DEF.match(lines[j][1].strip()) if lines[j][0] == "text" else None
                if m and m.group(1) == n:
                    labels.add(j)
                    break
            else:
                raise ValueError(f"label {n}{d} of {lines[i][1]!r} is not defined")
    return reloc, labels


def render_args(args, operands, indent="        "):
    return "".join(f"{indent}{a},\n" for a in args + operands)


# --- Compiling ----------------------------------------------------------------

def marker(fn, i, end=False):
    return f"vgpre{fn}_{i}{'e' if end else ''}"


def marked_source(text, functions):
    """`text` (a generated module) with markers in each function's code,
    recording each function's parsed template in `functions`."""
    def rewrite(m):
        lines, operands = parse_args(m.group(1))
        reloc, labels = kept_lines(lines)
        fn = len(functions)
        functions.append((lines, operands, reloc, labels))
        args = [literal(marker(fn, "s") + ":")]
        for i, (kind, t) in enumerate(lines):
            if i in reloc or i in labels:
                args.append(literal(marker(fn, i) + ":"))
            args.append(t if kind == "concat" else literal(t))
            if i in reloc:
                args.append(literal(marker(fn, i, True) + ":"))
        return "    core::arch::naked_asm!(\n" + render_args(args, operands) + "    )\n"
    return NAKED.sub(rewrite, text)


def build(src_dir, target, triple, workdir):
    """Compiles the crate whose sources are in `src_dir` (its root
    `lib.rs`) for `triple`, and returns its object files."""
    name = f"verified-garbage-asm-{target}"
    crate = workdir / "crate"
    crate.mkdir(parents=True, exist_ok=True)
    (crate / "Cargo.toml").write_text(f"""[package]
name = "{name}"
version = "0.0.0"
edition = "2024"
publish = false

[lib]
path = "{(src_dir / 'lib.rs').as_posix()}"

[dependencies]
verified-garbage-cpu = {{ path = "{CPU_CRATE.as_posix()}" }}

[workspace]
""")
    env = dict(os.environ, CARGO_TARGET_DIR=str(workdir / "target"), CARGO_INCREMENTAL="0",
               CARGO_PROFILE_DEV_DEBUG="0")
    for v in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET"):
        env.pop(v, None)
    subprocess.run(["cargo", "build", "--lib", "-q", "--target", triple, "--manifest-path",
                    str(crate / "Cargo.toml")], check=True, env=env)
    deps = workdir / "target" / triple / "debug" / "deps"
    rlibs = sorted(deps.glob(f"lib{name.replace('-', '_')}-*.rlib"), key=os.path.getmtime)
    members = objfile.ar_members(rlibs[-1].read_bytes())
    return [objfile.Elf(b) for n, b in members.items() if n.endswith(".o")]


def marker_offsets(objects):
    """Each marker's section's bytes and the marker's offset in it."""
    found = {}
    for o in objects:
        for s in o.symbols:
            if s.name.startswith("vgpre") and s.shndx < len(o.sections):
                found[s.name] = (o.sections[s.shndx], s.value)
    return found


# --- Encoding -------------------------------------------------------------------

def octa(b):
    out = []
    whole = len(b) - len(b) % 16
    vals = [f"0x{int.from_bytes(b[i:i + 16], 'little'):x}" for i in range(0, whole, 16)]
    out += [".octa " + ",".join(vals[i:i + 4]) for i in range(0, len(vals), 4)]
    if whole < len(b):
        out.append(".byte " + ",".join(str(x) for x in b[whole:]))
    return out


def encode(target, b):
    if not b:
        return []
    if target == "x86_64":
        return octa(b)
    raise ValueError(target)


# --- Writing `src/` -------------------------------------------------------------

def blobs(fn, lines, reloc, labels, found):
    """The runs of bytes of function `fn` between its kept lines, from the
    markers `found`: one per kept line, and one after the last."""
    section, start = found[marker(fn, "s")]
    data, cur, out = section.data, start, []
    for i in sorted(reloc | labels):
        sec, at = found[marker(fn, i)]
        assert sec is section
        out.append(data[cur:at])
        cur = found[marker(fn, i, True)][1] if i in reloc else at
    out.append(data[cur:section.size])
    return out


def preassembled(target, sources, found):
    """The text of each file of `src/`, given each file of `asm/` and the
    markers `found` of its compilation."""
    out, fn = {}, 0
    for rel, text in sources.items():
        def rewrite(m):
            nonlocal fn
            lines, operands = parse_args(m.group(1))
            reloc, labels = kept_lines(lines)
            runs = blobs(fn, lines, reloc, labels, found)
            fn += 1
            args = []
            for k, i in enumerate(sorted(reloc | labels)):
                if runs[k]:
                    args.append(literal("\n".join(encode(target, runs[k]))))
                kind, t = lines[i]
                args.append(t if kind == "concat" else literal(t))
            if runs[-1]:
                args.append(literal("\n".join(encode(target, runs[-1]))))
            return "    core::arch::naked_asm!(\n" + render_args(args, operands) + "    )\n"
        out[rel] = NAKED.sub(rewrite, text)
    return out


def sources_of(asm_dir):
    return {p.relative_to(asm_dir).as_posix(): p.read_text()
            for p in sorted(asm_dir.rglob("*.rs"))}


def generate(target, workdir):
    """The files of `src/` for `target`, from its `asm/`."""
    sources = sources_of(crate_dir(target) / "asm")
    functions, marked = [], workdir / "marked"
    for rel, text in sources.items():
        p = marked / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        new = marked_source(text, functions)
        if rel == "lib.rs":
            new = new.replace("\n#![no_std]\n", "\n#![no_std]\n#![allow(named_asm_labels)]\n", 1)
        p.write_text(new)
    found = marker_offsets(build(marked, target, TRIPLES[target], workdir / "build"))
    return preassembled(target, sources, found)


def main(argv):
    check = "--check" in argv
    targets = [a for a in argv if not a.startswith("--")] or list(TRIPLES)
    stale = []
    for target in targets:
        with tempfile.TemporaryDirectory() as d:
            files = generate(target, pathlib.Path(d))
        src = crate_dir(target) / "src"
        for rel, text in files.items():
            p = src / rel
            if check:
                if not p.exists() or p.read_text() != text:
                    stale.append(str(p.relative_to(ROOT)))
            else:
                p.parent.mkdir(parents=True, exist_ok=True)
                if not p.exists() or p.read_text() != text:
                    p.write_text(text)
        for p in sorted(src.rglob("*.rs")):
            if p.relative_to(src).as_posix() not in files:
                if check:
                    stale.append(f"{p.relative_to(ROOT)} (not generated)")
                else:
                    p.unlink()
        print(f"{target}: {len(files)} files", file=sys.stderr)
    for s in stale:
        print(f"{s} is out of date: run `python3 ci/preassemble.py`", file=sys.stderr)
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
