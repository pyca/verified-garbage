"""Chooses which architectures' benchmarks a change needs.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py
    python3 ci/bench_arches.py --all

Prints a JSON list of platforms (see `PLATFORMS`) for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.

A Rust file outside `src/asm/<arch>/` counts as changed on an architecture
only if what that architecture compiles of it changed: without comments,
items under a `cfg` that cannot hold there (one naming only other
architectures, e.g. PPC64LE's), and `cfg_attr`s that cannot apply. A `cfg`
that holds there is as if absent, so adding another architecture to a
module's list changes nothing. A `cfg` that depends on more than
`target_arch` and `target_endian` (a feature, `test`) is kept as written,
and a file this cannot follow counts as changed everywhere.

Each platform's `modules` narrows its benchmarks to the modules whose own
files changed:

  * `src/asm/<arch>/<module>.rs`: `<module>`, on that architecture;
  * `src/<module>.rs` or `src/hashes/<module>.rs`: `<module>`, and
    `src/hashes/mod.rs` (`streaming_hash!`, `HashFunction`): every hash
    module in `src/hashes/` (benchmarks of code built on a hash, such as
    HMAC, list that hash in their `USES`);
  * `src/<family>/<hash>.rs`: `<family>_<hash>` (as in `src/asm/`), and
    `src/<family>/mod.rs`: every `<family>_<hash>`;
  * a private module of the crate, `src/<helper>.rs` (`mod <helper>;` in
    `src/lib.rs`, used by none of the benchmarks, e.g. `ct`): the modules
    whose code names `crate::<helper>`;
  * a module only tests compile (`#[cfg(test)] mod <name>;`), or its
    declaration: none, also when it is new or removed;
  * `bench/benches/primitives/<name>.rs`, or its differential test
    `bench/tests/<name>.rs`: the modules in its `USES`, or for a helper
    without one (e.g. `mlkem.rs`, a macro), those of the benchmarks that
    call it.

A change to a file of `src/` only inside its tests (a top-level
`#[cfg(test)] mod`, which no benchmark compiles) needs nothing.

The benchmarks run those that use any of them, and all of them for a module
none uses (e.g. `lib`, or the generated `src/asm/<arch>/mod.rs`). Any
other shared change (e.g. executable code in benchmarks' `main.rs`, or a benchmark whose
`USES` cannot be read) leaves `modules` empty, which runs every benchmark.

A change to `src/cpu.rs` needs, on each architecture, the modules that
choose among implementations by a feature whose detection changed there:
the first feature each changed line names (the one it detects, as in
`let vaes = (ecx7 >> 9) & avx;`), in an item only one architecture (or a
few) compiles, such as its `runtime()`, or all its features if those lines
name none. A change to an item every architecture compiles (`Features`,
`detected()`) needs every module that chooses by a feature, on the
architectures detecting any; one to its tests, its comments or the names
appended to `NAMES` needs nothing. Its other code (choosing an
implementation once, when an object is created) is the same everywhere, so
measuring it where something is chosen suffices.

An architecture with primitives that choose among implementations by CPU
feature is benchmarked once with every feature the runner has, and once
more for each restriction in `CPU_FEATURES` (as `VG_CPU_FEATURES`, see
src/cpu.rs), so that every implementation is measured. Each entry's
`cpu-features` is its restriction, empty for none. With `--base REV`, edits
consisting only of module/benchmark registrations select their dependencies.

With a `BENCHMARKS_PER_JOB`, each configuration is split into jobs of at most
that many of the benchmarks it runs (`shard` is `i/n`, empty for one):
`bench_compare.py --shard` runs that share of them.

When only some benchmarks run, a configuration runs only if it can choose
other implementations of them than the configurations before it: one that
allows the same of the feature sets they choose by is left out. A benchmark
chooses by the features of each of its `USES` modules' generated variants
(a `_FEATURES` constant of `src/asm/<arch>/<module>.rs`) and by each feature
its architecture detects that their Rust code, but its tests, names in quotes
(e.g. `chacha20`'s `"neon"`), at base and at head. A module whose Rust code reads `VG_CPU_FEATURES` itself (on
AArch64, SHA-3 uses FEAT_SHA3 only when it is named) depends on which of its
features each configuration names. All benchmarks run every configuration.
"""

import difflib
import functools
import json
import pathlib
import subprocess
import re
import sys

# The architectures benchmarked, and where each one runs natively (as in
# ci.yml's `rust` job: the 32-bit ones in a 32-bit userspace container, built
# by ci/runner.Dockerfile, on the 64-bit host of the same family).
PLATFORMS = {
    "x86_64": {"os": "ubuntu-latest"},
    "aarch64": {"os": "ubuntu-24.04-arm"},
    "x86": {
        "os": "ubuntu-latest",
        "image": "ghcr.io/pyca/verified-garbage-runner:i686",
        "options": "--platform linux/386",
    },
    "arm": {
        "os": "ubuntu-24.04-arm",
        "image": "ghcr.io/pyca/verified-garbage-runner:armv7l",
        "options": "--platform linux/arm/v7",
    },
}

# The other `VG_CPU_FEATURES` each architecture is benchmarked with, so that
# each implementation a runner can run is measured (on x86-64, each of
# Ed25519's combinations of SHA-512 and field multiplication, and, on
# x86-64 and x86, AES-GCM's `_aesni` and `_pclmul`, which a runner with
# both extensions never chooses, and on x86-64 its `_aesni_pclmul`, its
# `_aesni_pclmul_avx` and the instances with VAES or VPCLMULQDQ alone or
# paired with the other's 128-bit instruction, which a runner with both never
# chooses, and with both in 256-bit registers alone, which a runner with
# AVX512BW never chooses; Argon2 with G's AVX-512 code and BLAKE2b's
# baseline code, which a runner with AVX2 never chooses, and with BLAKE2b's
# AVX2 code, which a runner with AVX512VL never chooses; RSAES-PKCS1-v1_5
# decryption with SHA-256's SHA extensions and RSA's baseline code, which a
# runner with ADX never chooses; on AArch64,
# ChaCha20's `_neon` instances, which the SVE2 runner never chooses; no
# runner has the SHA512 extension, whose variants only ci.yml tests, under
# SDE).
CPU_FEATURES = {
    "x86_64": [
        "avx,avx2,bmi1,bmi2,adx",
        "avx,avx2,bmi1,bmi2",
        "bmi2,adx",
        "sha,ssse3",
        "avx,avx2,bmi2,adx,avx512ifma,avx512vl",
        "aes,ssse3",
        "pclmulqdq,ssse3",
        "aes,pclmulqdq,ssse3",
        "aes,avx,pclmulqdq,ssse3",
        "aes,avx,avx2,ssse3,vaes",
        "avx,avx2,pclmulqdq,ssse3,vpclmulqdq",
        "aes,avx,avx2,pclmulqdq,ssse3,vaes",
        "aes,avx,avx2,pclmulqdq,ssse3,vpclmulqdq",
        "aes,avx,avx2,pclmulqdq,ssse3,vaes,vpclmulqdq",
        "avx,avx512f",
        "avx,avx2,avx512f",
        "none",
    ],
    "aarch64": ["neon", "sha3", "none"],
    "x86": ["aes", "pclmulqdq,ssse3", "none"],
}

# The benchmarks (`BENCHES` entries of bench/benches/primitives/main.rs) one
# job runs at most, or None for one job per configuration. Every runner takes
# about 1 s per benchmark id per pass; with 2 rounds (bench_compare.py), all
# 51 fit in one job on every runner, and each shard would add a job per
# configuration (with its own builds), so none is split for now.
BENCHMARKS_PER_JOB = None

# Changes to this script choose benchmarks but are not measured by any:
# `ci/test_check_benchmarks.py` tests it.
SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_compare\.py$"
    r"|\.github/workflows/bench\.yml$"
)


# The file of one module: its assembly on one architecture, or its Rust API
# on every one.
ASM = re.compile(r"src/asm/([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
API = re.compile(r"src/(?:hashes/)?([a-z0-9_]+)\.rs$")
HASHES = "src/hashes/mod.rs"
# A module declared in `src/lib.rs`: its attributes, and `pub` if it has it.
LIB_MOD = re.compile(r"^((?:#\[[^\n]*\]\n)*)(pub(?:\([a-z]+\))? )?mod ([a-z0-9_]+);", re.M)
FAMILY = re.compile(r"src/(?!asm/|hashes/)([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
# One algorithm's benchmark, and the modules it lists in its `USES`.
BENCH = re.compile(r"bench/benches/primitives/(?!main\.rs$)([a-z0-9_]+)\.rs$")
# A differential test of one algorithm's benchmark's API, next to it.
BENCH_TEST = re.compile(r"bench/tests/([a-z0-9_]+)\.rs$")
USES = re.compile(r"pub const USES: &\[&str\] = &\[([^\]]*)\];")
QUOTED = re.compile(r'"([a-z0-9_]+)"')
# A generated variant's CPU features (a `Features` constant, or a list of
# names at a base revision from before it was one), and the features
# `src/cpu.rs` knows.
FEATURES = re.compile(
    r"_FEATURES: (?:&\[&str\] = &\[|crate::cpu::Features = crate::cpu::Features::of\(&\[)([^\]]*)\]")
NAMES = re.compile(r"const NAMES: \[&str; \d+\] = \[([^\]]*)\];")
# Each architecture's feature detection in `src/cpu.rs`: its `cfg`, and the
# body, which names each feature in quotes or as a `let`.
RUNTIME = re.compile(r"(#\[cfg\([^\n]*\)\])\nfn runtime\(\) -> u32 \{\n(.*?)\n\}\n", re.S)
LET = re.compile(r"\blet ([a-z0-9_]+) =")
# A top-level module only tests compile: from its `#[cfg(test)]` to the `}`
# closing it, alone in column 0 as rustfmt writes it.
TEST_MOD = re.compile(r"^#\[cfg\(test\)\]\n(?:#\[[^\n]*\]\n)*(?:pub(?:\([a-z]+\))? )?mod [a-z0-9_]+ \{\n.*?^\}$",
                      re.M | re.S)
# Code choosing by what `VG_CPU_FEATURES` names, not only by what it allows.
OPT_IN = re.compile(r'var\("VG_CPU_FEATURES"\)')

# The first line of an item of `src/cpu.rs`: in column 0, and not a
# comment, an attribute or the end of an item.
ITEM_START = re.compile(r"(?!//|#\[|[\s})\]]|$)")

ALL = None


@functools.lru_cache(None)
def read(path, revision=None, root="."):
    if revision:
        result = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=root,
                                capture_output=True, text=True, check=False)
        return result.stdout if result.returncode == 0 else None
    try:
        return (pathlib.Path(root) / path).read_text()
    except FileNotFoundError:
        return None


def bench_uses(path, revision=None, root="."):
    text = read(path, revision, root)
    match = USES.search(text) if text is not None else None
    return set(re.findall(r'"([a-z0-9_]+)"', match[1])) if match else None


def bench_catalog(revision=None, root="."):
    main = read("bench/benches/primitives/main.rs", revision, root)
    names = set(re.findall(r"\(([a-z0-9_]+)::USES, \1::bench\)", main or ""))
    catalog = {name: bench_uses(f"bench/benches/primitives/{name}.rs", revision, root)
               for name in names}
    return catalog if catalog and all(catalog.values()) else None


def bench_count(modules, root="."):
    """How many benchmarks run for `modules` (ALL: every registered one)."""
    main = read("bench/benches/primitives/main.rs", None, root) or ""
    names = set(re.findall(r"\(([a-z0-9_]+)::USES, \1::bench\)", main))
    if modules is ALL:
        return len(names)
    catalog = bench_catalog(None, root) or {}
    return sum(1 for uses in catalog.values() if uses & modules)


def test_lines(text):
    """The (0-based) numbers of the lines of `text` in its test modules."""
    lines = set()
    for m in TEST_MOD.finditer(text):
        first = text.count("\n", 0, m.start())
        lines.update(range(first, first + m[0].count("\n") + 1))
    return lines


def without_tests(text):
    """`text` without its test modules."""
    return TEST_MOD.sub("", text)


def tests_only(path, base):
    """Whether `path` changed since `base` only inside its test modules."""
    old, new = (read(path, base) if base else None), read(path)
    if old is None or new is None or old == new:
        return False
    sides = [old.splitlines(), new.splitlines()]
    tests = [test_lines(old), test_lines(new)]
    matcher = difflib.SequenceMatcher(None, *sides, autojunk=False)
    return all(set(range(i1, i2)) <= tests[0] and set(range(j1, j2)) <= tests[1]
               for tag, i1, i2, j1, j2 in matcher.get_opcodes() if tag != "equal")


def registrations(path, base, arch):
    """Only changed module declarations/registry entries, as `arch` compiles
    them; other code means all. A declaration added or removed with its
    `#[cfg(test)]` declares a module no benchmark compiles, which needs
    nothing; the attribute alone may change what they compile."""
    if not base:
        return None
    try:
        sides = [with_test_attributes(for_arch(read(path, r), arch)) for r in (base, None)]
    except Unreadable:
        return None
    names = set()
    matcher = difflib.SequenceMatcher(None, *sides, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        for line in sides[0][i1:i2] + sides[1][j1:j2] if tag != "equal" else ():
            test = line.startswith(TEST_ATTRIBUTE + " ")
            if test:
                line = line[len(TEST_ATTRIBUTE) + 1:]
            elif line == "#[rustfmt::skip]":
                continue
            match = re.fullmatch(r"(?:pub(?:\(crate\))? )?mod (\w+);|\((\w+)::USES, \2::bench\),", line)
            if not match or (test and not match[1]):
                return None
            if not test:
                names.add(match[1] or match[2])
    return names


TEST_ATTRIBUTE = "#[cfg(test)]"


def with_test_attributes(lines):
    """`lines` with each `#[cfg(test)]` joined to the line after it, so that
    a diff keeps them together."""
    out = []
    for line in lines:
        if out and out[-1] == TEST_ATTRIBUTE:
            out[-1] += " " + line
        else:
            out.append(line)
    return out


class Unreadable(Exception):
    """Rust that `for_arch` cannot follow."""


# A literal whose contents could look like code: a (byte) string, raw or
# not, or a character.
RAW = re.compile(r'(?<![A-Za-z0-9_])b?r(#*)"')
STRING = re.compile(r'(?<![A-Za-z0-9_])b?"(?:[^"\\]|\\.)*"', re.S)
CHAR = re.compile(r"(?<![A-Za-z0-9_])b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")
# An attribute that `for_arch` evaluates: `#[cfg(`, `#![cfg_attr(`, ….
CFG_ATTR = re.compile(r"#(!?)\[\s*(cfg|cfg_attr)\s*\(")
# The `target_endian` of every benchmarked architecture.
ENDIAN = "little"


def literal_end(text, i):
    """The end of the literal starting at `i`, or None if none does."""
    if m := RAW.match(text, i):
        end = text.find('"' + m[1], m.end())
        if end < 0:
            raise Unreadable
        return end + 1 + len(m[1])
    if text[i] in "\"b" and (m := STRING.match(text, i)):
        return m.end()
    if text[i] == '"':
        raise Unreadable
    m = CHAR.match(text, i)
    return m.end() if m else None


def without_comments(text):
    out, i = [], 0
    while i < len(text):
        if text.startswith("//", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0 or "/*" in text[i + 2:end]:
                raise Unreadable
            out.append(" ")
            i = end + 2
        elif (end := literal_end(text, i)) is not None:
            out.append(text[i:end])
            i = end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def closing(text, i):
    """The end of the brackets opening at `i`."""
    depth = 0
    while i < len(text):
        if (end := literal_end(text, i)) is not None:
            i = end
            continue
        if text[i] in "([{":
            depth += 1
        elif text[i] in ")]}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise Unreadable


def item_end(text, i):
    """The end of the item (or field, variant, arm, statement) starting at
    `i`. It may end early (e.g. at the `,` of `impl<A, B>`), which leaves the
    rest of it in, never late."""
    depth = 0
    while i < len(text):
        if (end := literal_end(text, i)) is not None:
            i = end
            continue
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                return i
            depth -= 1
            if depth == 0 and c == "}":
                return i + 1
        elif c in ";," and depth == 0:
            return i + 1
        i += 1
    return i


def split_top(text):
    """`text` split at its commas outside brackets."""
    parts, depth, start = [], 0, 0
    for i, c in enumerate(text):
        depth += (c in "([{") - (c in ")]}")
        if c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def cfg_value(predicate, arch):
    """Whether a `cfg` predicate holds on `arch`: None if that depends on
    more than the architecture (a feature, `test`, …)."""
    if m := re.fullmatch(r'(\w+)\s*=\s*"([^"]*)"', predicate):
        return {"target_arch": m[2] == arch, "target_endian": m[2] == ENDIAN}.get(m[1])
    if m := re.fullmatch(r"(all|any|not)\s*\((.*)\)", predicate, re.S):
        values = [cfg_value(p, arch) for p in split_top(m[2])]
        if m[1] == "not":
            if len(values) != 1:
                raise Unreadable
            return None if values[0] is None else not values[0]
        decisive = m[1] == "any"
        if decisive in values:
            return decisive
        return None if None in values else not decisive
    if re.fullmatch(r"\w+", predicate):
        return None
    raise Unreadable


def for_arch(text, arch):
    """The lines of `text` that `arch` compiles, without comments: an item
    whose `cfg` does not hold there is left out (a whole file, for one of
    its inner `cfg`s), as is a `cfg` that holds, and a `cfg_attr` that does
    not. A missing file is empty."""
    if text is None:
        return []
    text = without_comments(text)
    out, i = [], 0
    while i < len(text):
        if (end := literal_end(text, i)) is not None:
            out.append(text[i:end])
            i = end
            continue
        m = CFG_ATTR.match(text, i)
        if not m:
            out.append(text[i])
            i += 1
            continue
        end = closing(text, m.end() - 1)
        close = re.compile(r"\s*\]").match(text, end)
        if not close:
            raise Unreadable
        args = split_top(text[m.end():end - 1])
        if not args or (m[2] == "cfg") != (len(args) == 1):
            raise Unreadable
        value = cfg_value(args[0], arch)
        if value is None or (m[2] == "cfg_attr" and value):
            out.append(text[i:close.end()])
            i = close.end()
        elif m[2] == "cfg_attr" or value:
            i = close.end()
        elif m[1]:
            # An inner `cfg` that does not hold: of the file, if only inner
            # attributes come before it.
            if not re.fullmatch(r"(\s*#!\[[^\n]*\])*\s*", "".join(out)):
                raise Unreadable
            return []
        else:
            i = item_end(text, close.end())
    return [line.strip() for line in "".join(out).splitlines() if line.strip()]


def affected(path, base):
    """The benchmarked architectures that compile `path` differently at
    `base` and now: all of them for a file that is not Rust, cannot be
    read, or did not change."""
    old, new = (read(path, base) if base else None), read(path)
    if not path.endswith(".rs") or old == new:
        return list(PLATFORMS)
    try:
        return [a for a in PLATFORMS if for_arch(old, a) != for_arch(new, a)]
    except Unreadable:
        return list(PLATFORMS)


def members(family, known):
    """The modules of a family: `<family>_<hash>`."""
    return {m for m in known if m.startswith(f"{family}_")}


def rust_files(root="."):
    return sorted(p.relative_to(root).as_posix() for p in pathlib.Path(root, "src").glob("**/*.rs"))


def hashes(root="."):
    """The hash modules: the files of `src/hashes/` but its `mod.rs`."""
    return {m[1] for path in rust_files(root)
            if (m := re.fullmatch(r"src/hashes/([a-z0-9_]+)\.rs", path)) and m[1] != "mod"}


def lib_modules(revision=None, root="."):
    """The modules `src/lib.rs` declares: for each, whether only tests
    compile it, and whether it is public."""
    return {m[3]: ("#[cfg(test)]" in m[1], bool(m[2]))
            for m in LIB_MOD.finditer(read("src/lib.rs", revision, root) or "")}


def test_only(module, base=None):
    """Whether only tests compile `module` (at `base` too, if given, or it
    is new or removed there), so no benchmark can measure it."""
    declared = [lib_modules(r).get(module) for r in ([base, None] if base else [None])]
    return any(declared) and all(d is None or d[0] for d in declared)


def users(family, known, root="."):
    """The modules whose Rust code (outside the family's) uses the family's
    shared code, or a private module of the crate; a file that is no
    module's names itself, which no benchmark uses. Modules only tests
    compile are left out."""
    names = set()
    tests = {m for m, (test, _) in lib_modules(None, root).items() if test}
    for path in rust_files(root):
        if path.startswith(("src/asm/", f"src/{family}/")) or path == f"src/{family}.rs" or not re.search(
                rf"\b(?:crate|super)::{family}::", read(path, None, root) or ""):
            continue
        api, other = API.match(path), FAMILY.match(path)
        if path == HASHES:
            names |= hashes(root)
        elif api:
            if api[1] not in tests:
                names.add(api[1])
        elif other and other[2] == "mod":
            names |= members(other[1], known) or {path}
        else:
            names.add(f"{other[1]}_{other[2]}" if other else path)
    return names


def helper_uses(name, catalog):
    """The `USES` of the benchmarks that call the helper
    `bench/benches/primitives/<name>.rs` (a module of `main.rs` without
    `USES` of its own), or None if none does."""
    text = read(f"bench/benches/primitives/{name}.rs")
    if text is None or not catalog:
        return None
    macros = re.findall(r"macro_rules! ([a-z0-9_]+)", text)
    calls = re.compile(r"\b(?:%s)" % "|".join([rf"{name}::", *(rf"{m}!" for m in macros)]))
    uses = set().union(*(u for n, u in catalog.items()
                         if n != name and calls.search(read(f"bench/benches/primitives/{n}.rs") or "")))
    return uses or None


def sources(module):
    """The Rust files that can choose among `module`'s implementations."""
    paths = [f"src/{module}.rs", f"src/{module}/mod.rs", f"src/hashes/{module}.rs", "src/hashes/mod.rs"]
    family, _, hash_ = module.partition("_")
    if hash_:
        paths += [f"src/{family}/{hash_}.rs", f"src/{family}/mod.rs"]
    return paths


def detectable(arch, cpu):
    """The features `src/cpu.rs` (the text `cpu`) can detect on `arch`, from
    its `runtime()` for that architecture, or None if there is none."""
    names = NAMES.search(cpu)
    if not names:
        return None
    known = set(QUOTED.findall(names[1]))
    found = None
    for cfg, body in RUNTIME.findall(cpu):
        if arch in re.findall(r'target_arch = "([a-z0-9_]+)"', cfg):
            found = (found or set()) | (set(QUOTED.findall(body)) | set(LET.findall(body))) & known
    return found


def requirements(arch, modules, revisions):
    """The sets of CPU features that choose among `modules`' implementations
    on `arch`, at any of `revisions`: each variant's, and each feature named
    in their Rust code alone; with `<name>!` for a feature that chooses only
    when `VG_CPU_FEATURES` names it. None if the features `arch` can detect
    cannot be read."""
    reqs = set()
    for revision in revisions:
        arch_features = detectable(arch, read("src/cpu.rs", revision) or "")
        if arch_features is None:
            return None if CPU_FEATURES.get(arch) else set()
        quoted = re.compile(r'"(%s)"' % "|".join(map(re.escape, sorted(arch_features))))
        for module in modules:
            asm = read(f"src/asm/{arch}/{module}.rs", revision) or ""
            found = {frozenset(QUOTED.findall(lst)) for lst in FEATURES.findall(asm)}
            opt_in = False
            for path in sources(module):
                text = without_tests(read(path, revision) or "")
                if arch_features:
                    found |= {frozenset([name]) for name in quoted.findall(text)}
                opt_in |= bool(OPT_IN.search(text))
            found = {req for req in found if req and req <= arch_features}
            reqs |= {req | {f"{name}!" for name in req} for req in found} if opt_in else found
    return reqs


def allows(restriction, reqs):
    """Which of `reqs` a `VG_CPU_FEATURES` of `restriction` allows (on a CPU
    with every feature)."""
    named = set() if restriction in ("", "none") else set(restriction.split(","))

    def allowed(feature):
        if feature.endswith("!"):
            return feature[:-1] in named
        return not restriction or feature in named
    return frozenset(req for req in reqs if all(map(allowed, req)))


def arches(changed, base=None):
    # The modules to benchmark on each architecture that needs it, or ALL.
    needed = {}
    catalogs = [bench_catalog(base), bench_catalog()]
    known = set().union(*catalogs[-1].values()) if catalogs[-1] else set()

    def need(arch, module):
        if module not in known:
            needed[arch] = ALL
        elif needed.get(arch, set()) is not ALL:
            needed.setdefault(arch, set()).add(module)

    for path in changed:
        asm, api, family = ASM.match(path), API.match(path), FAMILY.match(path)
        if path.startswith("src/") and not asm and tests_only(path, base):
            continue
        # A change to code only other architectures compile (e.g. PPC64LE's)
        # needs nothing.
        targets = [asm[1]] if asm else affected(path, base)
        if path in ("src/lib.rs", "bench/benches/primitives/main.rs") or (asm and asm[2] == "mod"):
            for arch in targets:
                names = registrations(path, base, arch)
                if names is None:
                    needed[arch] = ALL
                for name in names or ():
                    if path.startswith("bench/"):
                        uses = set().union(*(c.get(name, set()) for c in catalogs if c))
                        if not uses:
                            needed[arch] = ALL
                        for module in uses:
                            need(arch, module)
                    else:
                        need(arch, name)
        elif path == "src/cpu.rs":
            changes = cpu_changes(base)
            for a in targets:
                if changes is None:
                    needed[a] = ALL
                    continue
                if "*" not in changes and a not in changes:
                    continue
                modules = cpu_modules(a, ALL if "*" in changes else changes[a], known,
                                      [base, None] if base else [None])
                if modules is None:
                    needed[a] = ALL
                for module in modules or ():
                    need(a, module)
        elif asm and asm[1] in PLATFORMS:
            need(asm[1], asm[2])
        elif path == HASHES:
            for a in targets:
                for name in hashes():
                    need(a, name)
        elif api and path == f"src/{api[1]}.rs" and test_only(api[1], base):
            continue
        elif (api and path == f"src/{api[1]}.rs" and api[1] not in known
              and lib_modules().get(api[1], (False, True)) == (False, False)):
            # A private helper: only the crate's own modules can use it.
            names = users(api[1], known)
            for a in targets:
                if not names:
                    needed[a] = ALL
                for name in names:
                    need(a, name)
        elif api:
            for a in targets:
                need(a, api[1])
        elif family:
            # A family's `mod.rs` is the code its `<family>_<hash>` modules
            # share, which others may use too; with no module, every
            # benchmark runs.
            names = ((members(family[1], known) | users(family[1], known)) or {family[1]}
                     if family[2] == "mod" else {f"{family[1]}_{family[2]}"})
            for a in targets:
                for name in names:
                    need(a, name)
        elif (bench := BENCH.match(path) or BENCH_TEST.match(path)) and (
                uses := bench_uses(f"bench/benches/primitives/{bench[1]}.rs")
                or helper_uses(bench[1], catalogs[-1])):
            for a in targets:
                for m in uses:
                    need(a, m)
        elif SHARED.match(path):
            for a in targets:
                needed[a] = ALL
    revisions = [base, None] if base else [None]
    return [p for a in PLATFORMS if a in needed
            for p in platforms(a, needed[a], run_requirements(a, needed[a], catalogs, revisions),
                               bench_count(needed[a]))]


def cpu_item(lines, i):
    """The item of `src/cpu.rs` (as `lines`) line `i` is in: its first line,
    and its attributes."""
    while i < len(lines) - 1 and lines[i].startswith("#["):  # The next item's.
        i += 1
    while i > 0 and not ITEM_START.match(lines[i]):
        i -= 1
    attributes = []
    j = i - 1
    while j >= 0 and lines[j].startswith(("#[", "///")):
        attributes += [lines[j]] if lines[j].startswith("#[") else []
        j -= 1
    return lines[i], attributes


def cpu_changes(base):
    """What the change to `src/cpu.rs` since `base` affects: for each
    architecture whose own detection changed, the first feature each changed
    line names (ALL if none does); "*" for a change to code every
    architecture compiles; None if either revision cannot be read."""
    old, new = read("src/cpu.rs", base) if base else None, read("src/cpu.rs")
    if old is None or new is None:
        return None
    names = [QUOTED.findall(m[1]) if (m := NAMES.search(t)) else [] for t in (old, new)]
    known = set(names[0]) | set(names[1])
    sides = [old.splitlines(), new.splitlines()]
    items = {}
    matcher = difflib.SequenceMatcher(None, *sides, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        for side, lo, hi in ((0, i1, i2), (1, j1, j2)):
            for k in range(lo, hi):
                code = sides[side][k].split("//")[0].strip()
                if not code:
                    continue
                first, attributes = cpu_item(sides[side], k)
                cfgs = [a for a in attributes if a.startswith("#[cfg(")]
                if "#[cfg(test)]" in cfgs:
                    continue
                if re.search(r"\bconst NAMES\b", first):
                    # Names appended change no other feature's bit, and
                    # choose nothing until something detects them.
                    a, b = names
                    if a == b[:len(a)] or b == a[:len(b)]:
                        continue
                    arches = "*"
                else:
                    arches = frozenset(re.findall(r'target_arch = "([a-z0-9_]+)"', " ".join(cfgs)))
                    if not arches or any("not(" in c for c in cfgs):
                        arches = "*"
                key = (arches, first.strip())
                # The feature a line detects comes first (`let vaes = … & avx`).
                named = [n for n in re.findall(r"[a-z0-9_]+", code) if n in known]
                items.setdefault(key, set()).update(named[:1])
    changes = {}
    for (arches, _), features in items.items():
        for arch in [arches] if arches == "*" else arches:
            if not features or arches == "*":
                changes[arch] = ALL
            elif changes.get(arch, set()) is not ALL:
                changes.setdefault(arch, set()).update(features)
    return changes


def cpu_modules(arch, changes, known, revisions):
    """The modules `known` on `arch` that choose by a feature in `changes`
    (ALL: by any), or None if what they choose by cannot be read."""
    modules = set()
    for module in sorted(known):
        reqs = requirements(arch, {module}, revisions)
        if reqs is None:
            return None
        if any(changes is ALL or {f.rstrip("!") for f in req} & changes for req in reqs):
            modules.add(module)
    return modules


def run_requirements(arch, modules, catalogs, revisions):
    """The `requirements` of the benchmarks that use any of `modules`, or
    None (every configuration) for all of them or an unreadable catalog."""
    if modules is ALL or not all(catalogs):
        return None
    uses = {m for c in catalogs for u in c.values() if u & modules for m in u}
    return requirements(arch, uses, revisions)


def platforms(arch, modules=ALL, reqs=None, benchmarks=None):
    """The matrix entries of `arch`: one per CPU feature configuration, but
    with `reqs`, only the first of those allowing the same of them; each in
    as many shards as `benchmarks` (by default, every registered one)
    needs."""
    if benchmarks is None:
        benchmarks = bench_count(ALL)
    shards = max(1, -(-benchmarks // BENCHMARKS_PER_JOB)) if BENCHMARKS_PER_JOB else 1
    configurations = ["", *CPU_FEATURES.get(arch, [])]
    if reqs is not None:
        chosen = {}
        for features in configurations:
            allowed = allows(features, reqs)
            # One allowing none of them is the one that names none.
            if allowed not in chosen or (features == "none" and chosen[allowed]):
                chosen[allowed] = features
        configurations = [f for f in configurations if f in chosen.values()]
    return [
        {
            "arch": arch,
            **PLATFORMS[arch],
            "cpu-features": features,
            "modules": " ".join(sorted(modules or ())),
            "shard": f"{shard}/{shards}" if shards > 1 else "",
        }
        for features in configurations
        for shard in range(1, shards + 1)
    ]


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        matrix = [p for a in PLATFORMS for p in platforms(a)]
    else:
        if sys.argv[1:] and (len(sys.argv) != 3 or sys.argv[1] != "--base"):
            sys.exit("usage: bench_arches.py [--all | --base REV]")
        matrix = arches(sys.stdin.read().split(), sys.argv[2] if len(sys.argv) == 3 else None)
    print(json.dumps(matrix))
