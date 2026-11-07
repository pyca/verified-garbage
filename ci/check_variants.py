#!/usr/bin/env python3
"""Checks that every implementation of a verified function reaches every
function built on it, from the generated code, each target's
`crates/verified-garbage-asm-<target>/src/`.

A primitive can have several implementations with the same contract, e.g.
`vg_sha256_compress` and `vg_sha256_compress_shani`: a *variant* of a
function `f` on a target is a function of that target named `f_<suffix>`
with the same Rust signature (`_shani`, `_avx2`, …).

* **Variants flow to callers.** If a function `g` calls `f`, and `f` has a
  variant `f_<s>`, then `g` must have the variant `g_<s>`, and `g_<s>` must
  not call the baseline `f`: it calls `f_<s>`, or none of `f`'s
  implementations, when it does the work itself (e.g. ML-KEM's AArch64
  `vg_mlkem768_keygen_x2_sha3`, which runs two Keccak permutations at once
  with `vg_keccak_f1600_x2_sha3` rather than calling the sponge functions
  `vg_keccak_absorb_scratch_sha3`, … that `vg_mlkem768_keygen` calls the
  baseline of). (A variant may call the function it is a variant of, e.g.
  for a tail it leaves to the baseline code.) A function whose variant
  nothing would call needs none: one the Rust code does not use, all of
  whose callers have variants for `f_<s>` that do not call it, or need
  none themselves (`vg_mlkem_sample_ntt`, which `vg_mlkem768_keygen`, …
  call, but not their `_x2_sha3` variants). Nor does a function with
  implementations, but its baseline, that a CPU with `f_<s>`'s features
  runs, if there are some and none calls any of `f`'s implementations
  (AES-CBC's sequential encryption: its AES-NI code calls no
  `vg_aes_encrypt_blocks`, and serves CPUs with VAES too). Variants compose: a variant
  of a variant, `g_<t>_<s>`, has both suffixes, in either order, so when
  `g_<t>` calls `f`, its variant for `f_<s>` may be `g_<t>_<s>` or
  `g_<s>_<t>` (e.g. Ed25519's operations over each SHA-512 backend and each
  field multiplication: `vg_ed25519_verify_avx2_adx` is the variant both of
  `vg_ed25519_verify_avx2` for `vg_ed25519_verify_equation_adx` and of
  `vg_ed25519_verify_adx` for `vg_sha512_update_avx2`).
  A caller generic over several interfaces qualifies each suffix with a tag
  for its interface (`Emit.qualifiedName` in `lean/VerifiedGarbage/TCB/Emit.lean`),
  since two interfaces may have variants with the same suffix: its variant
  for `f_<s>` may add `<tag>_<s>` instead (`vg_argon2_g_avx512`, the
  variant of `vg_argon2` for `vg_argon2_compress_avx512`), and one of its
  variants adding a part ending in `_<s>` must not call `f`.
* **Every variant is used.** Each variant is called by another generated
  function or used by the Rust code of the library (`src/`), not counting
  its tests: the generated modules allow dead
  code, so a variant the Rust dispatch forgot would otherwise go unnoticed,
  and a variant only a test calls is one nothing else runs. Test code is
  every item gated by a `cfg` that requires `test` (`#[cfg(test)]`,
  `#[cfg(all(test, …))]`, an inner `#![cfg(test)]`) or marked `#[test]`,
  and every file such a `mod` declaration names, with the files it
  declares in turn. (Code a macro expands only in its tests, from an
  argument passed outside them, is not found: name such functions only in
  the test.)
* **Callers reach the best callee.** If a function `g` needs the CPU
  features `F` (its `VG_<G>_FEATURES`, none for a baseline) and calls `f`,
  and `f` has an implementation `f_<s>` whose features are more than those
  of the one `g` calls but all in `F`, then some implementation of `g`
  calls `f_<s>` (or one with still more features): otherwise no CPU ever
  runs `f_<s>` under `g`, however many features it has. A choice made by
  hand rather than by the generic registrations is what this catches
  (`vg_rsa_private_checked_ifma` calling `vg_rsa_public_precomputed_checked_adx`,
  its variant's `pubOp`, when `vg_rsa_public_precomputed_checked_ifma`
  needs only its features). The implementation `g` calls need not be the
  best itself: a caller generic over several interfaces has a variant for
  each combination (`…_sha224_shani` calls SHA-1's baseline,
  `…_sha224_shani_mgf1_shani` its `_shani`), and the Rust code chooses
  among them. A variant calling the function it is a variant of is exempt,
  as above.

Where the caller's function has a dispatcher, a variant of `g` for `f_<s>`
need not have a name of its own: it is enough that the dispatcher, on a CPU
with `g`'s features and `f_<s>`'s (and AVX2, where they include BMI2 or ADX,
which CPU detection reports only with it), runs an implementation that calls
`f_<s>`, one `f`'s dispatcher tries before it, or none of `f`'s
implementations (AES-GCM-SIV's `vg_aes_gcm_siv_seal_vaes_pclmul_avx2` for
`vg_aes_gcm_siv_seal_pclmul` and `vg_aes_ctr32_vaes`). An arm whose
condition depends on the compilation target (`cfg!`) is not counted.

A combination no CPU can choose is not required. When the Rust code never
chooses an implementation `c` on a CPU with all of the features of a set
`X` (it chooses another implementation of the same function there:
ChaCha20's 4-way SSSE3 code is not chosen with AVX and AVX2, which its
`_avx2` code needs), `NEVER_WITH` lists `X` for `c`. A variant of a
function `g` that runs `c` (`g` is `c` or calls it) for a callee's variant
`f_<s>` would run only on CPUs with both `g`'s features and `f_<s>`'s; if
those include one of `c`'s sets, the Rust code never chooses `c` there, so
no CPU chooses that combination, and `g_<s>` is not required. The Rust
code's choice is unit-tested both ways (CLAUDE.md), and each entry must
name a function of its target whose own features include none of its sets
(otherwise the Rust code could never choose it at all).

An *internal function* (`Rust.Internal` in `lean/VerifiedGarbage/TCB/Rust.lean`),
which the emitter writes to `src/internal/<name>.rs` of its crate, is code
that verified functions call but that has no contract: it has no Rust
signature (`fn <name>()`), so its variants are not found by their
signature. A variant of an internal function `f` is the internal function
`f_<suffix>` whose suffix is the suffix of a variant of a function with a
signature on the target (`_shani`, `_avx2`, `_blake2b_avx2`, …), or a
qualified part `_<tag>_<suffix>` of one whose `<suffix>` is one
(`_sha1_avx_bmi` of `_sha1_avx_bmi_sha256_avx2`), each
variant of a variant adding one: `vg_p384_mul_mod_n` is not a variant of
`vg_p384_mul`, as no function of a signature has a variant `_mod_n`, nor
`vg_keccak_f1600_x2` of `vg_keccak_f1600`, as none has a variant `_x2`
(though ML-KEM's have `_x2_sha3`). Its CPU features are in a `_FEATURES`
constant of its file, as an artifact's.

A function the emitter renders as another name of an identical function of
its module (`pub use self::<f> as <name>;`, `Rust.alias` in
`lean/VerifiedGarbage/TCB/Rust.lean`) is that function's code: it has its
signature and callees, and a use of it is a use of that function.

A *dispatcher* (`<f>_auto` in `dispatch/<module>.rs`, `Rust.dispatcher`: an
ordinary Rust function, `pub unsafe fn`, or for a function with one
implementation another name of it, `pub use crate::<module>::<f> as <f>_auto;`) runs the best of `f`'s implementations
the CPU supports. It is not a variant, and its calls are not those of a
generated function: a use of it by the Rust code is a use of each
implementation it calls, so that a variant whose dispatcher nothing uses is
not used either.

See "An optimized implementation reaches everything built on it" in
CLAUDE.md.
"""

import pathlib
import re
import sys

import asm_layout

ROOT = pathlib.Path(__file__).resolve().parent.parent

# A function's header; its body ends at the first line starting with `}`.
# Generated items are `pub`, in a target's crate, or `pub(crate)`, as the
# emitter wrote them when they were modules of the library.
FN = re.compile(
    r"^pub(?:\(crate\))? unsafe extern \"[\w-]+\" fn (vg_\w+)\((.*?)\)(?: -> ([^{]+?))? \{\n",
    re.MULTILINE | re.DOTALL,
)
# Another name of a function of the same module (`Rust.alias`).
ALIAS = re.compile(r"^pub(?:\(crate\))? use self::(vg_\w+) as (vg_\w+);$", re.MULTILINE)
# The dispatcher of a function with one implementation (`<f>_auto`,
# `Rust.soleDispatcher`), in `dispatch/<module>.rs`.
SOLE = re.compile(r"^pub use crate::\w+::(vg_\w+) as (vg_\w+);$", re.MULTILINE)
# A dispatcher (`Rust.dispatcher`), to the end of its body, and each function it calls.
DISPATCHER = re.compile(r"^pub unsafe fn (vg_\w+)\(.*?^\}\n", re.MULTILINE | re.DOTALL)
DISPATCHED = re.compile(r"unsafe \{ crate::\w+::(vg_\w+)\(")
# `<operand> = sym <path>`, found from the literal ` = sym ` (a leading
# `\w+` would be tried at every word character of the code: 30 times slower).
SYM = re.compile(r" = sym (?:\w+::)*(vg_\w+)")
WORD = re.compile(r"\w")
FEATURES = re.compile(
    r"^pub(?:\(crate\))? const (VG_\w+)_FEATURES: (?:crate::cpu|verified_garbage_cpu)::Features = "
    r"(?:crate::cpu|verified_garbage_cpu)::Features\((.*?)\);",
    re.MULTILINE,
)


def sources():
    """Each generated file's target and text: its modules', its internal
    functions' (`internal/<name>.rs`) and its dispatchers' (`dispatch/<module>.rs`)."""
    return [(target, path.read_text())
            for target, d in asm_layout.target_dirs(ROOT).items()
            for path in sorted(d.glob("*.rs")) + sorted(d.glob("internal/vg_*.rs"))
            + sorted(d.glob("dispatch/*.rs"))]


def bodies(text):
    """Each generated function's name, parameters, return type and body."""
    pos = 0
    while m := FN.search(text, pos):
        start = m.end()
        end = start if text.startswith("}", start) else text.find("\n}", start) + 1
        if not end:
            return
        yield (*m.groups(), text[start:end])
        pos = end


def callees(body):
    return {m.group(1) for m in SYM.finditer(body) if m.start() and WORD.match(body, m.start() - 1)}


def functions(srcs):
    """For each target, each generated function's signature and callees."""
    targets = {}
    for target, text in srcs:
        fns = targets.setdefault(target, {})
        for name, params, ret, body in bodies(text):
            fns[name] = ((params, (ret or "").strip()), callees(body))
        for name, canon in aliases(text).items():
            fns[name] = fns[canon]
    return targets


def aliases(text):
    """Each other name of a function of a generated file (`Rust.alias`), by
    the name it gives it: `{name: function}`; not a dispatcher's."""
    return {m.group(2): m.group(1) for m in ALIAS.finditer(text)}


def file_dispatchers(text):
    """Each dispatcher of a generated file (`Rust.dispatcher`), with the
    functions it calls: `{name: {function, …}}`."""
    out = {m.group(1): set(DISPATCHED.findall(m.group(0))) for m in DISPATCHER.finditer(text)}
    out.update({m.group(2): {m.group(1)} for m in SOLE.finditer(text)})
    return out


def dispatchers(srcs):
    """For each target, `file_dispatchers` of its files together."""
    targets = {}
    for target, text in srcs:
        targets.setdefault(target, {}).update(file_dispatchers(text))
    return targets


# An arm of a dispatcher: its condition and the function it returns.
ARM = re.compile(
    r"if (?P<cond>[^\n]*cpu\.contains\([^\n]*\)) \{\n(?:\s*//[^\n]*\n)*"
    r"\s*return unsafe \{ crate::\w+::(?P<fn>vg_\w+)\(")
BASE_CALL = re.compile(r"\n    unsafe \{ crate::\w+::(vg_\w+)\(")


def file_arms(text):
    """Each dispatcher of a generated file (`Rust.dispatcher`) as the
    implementations it tries, in order, each with the CPU features its
    condition names (its `_FEATURES` constant's, read from `features`, and
    any others it names) and whether the condition also depends on the
    compilation target (`cfg!`), then its base: `{name: ([(function,
    {constant, …}, {feature, …}, by_target), …], base)}`."""
    out = {}
    for m in DISPATCHER.finditer(text):
        body = m.group(0)
        arms = [(a.group("fn"),
                 {c.lower() for c in re.findall(r"(VG_\w+)_FEATURES", a.group("cond"))},
                 {f.lower() for f in re.findall(r"feature::(\w+)", a.group("cond"))},
                 "cfg!(" in a.group("cond"))
                for a in ARM.finditer(body)]
        base = BASE_CALL.findall(body)
        out[m.group(1)] = (arms, base[-1] if base else None)
    return out


def all_arms(srcs):
    """For each target, `file_arms` of its files together."""
    targets = {}
    for target, text in srcs:
        targets.setdefault(target, {}).update(file_arms(text))
    return targets


def all_aliases(srcs):
    """For each target, `aliases` of its files together."""
    targets = {}
    for target, text in srcs:
        targets.setdefault(target, {}).update(aliases(text))
    return targets


def features(srcs):
    """For each target, the CPU features each generated function needs, by
    its name (functions that need none are left out)."""
    targets = {}
    for target, text in srcs:
        feats = targets.setdefault(target, {})
        for m in FEATURES.finditer(text):
            feats[m.group(1).lower()] = frozenset(
                f.lower() for f in re.findall(r"(?:crate::cpu|verified_garbage_cpu)::feature::(\w+)", m.group(2)))
    return targets


# The signature of an internal function (`fn <name>()`).
INTERNAL = ("", "")

# For each target, the implementations the Rust code never chooses on a CPU
# with all of the features of one of the sets listed (in lower case, as
# `features` reads them), because it chooses another implementation of the
# same function there: a combination with one of them that needs all of a
# set is one no CPU chooses (see the module's docstring).
NEVER_WITH = {
    # The dispatchers of ChaCha20 and ChaCha20-Poly1305 rank `_avx2` (and
    # better) above `_ssse3` (`VG.Dispatch.ranking`), so choose it whenever
    # AVX2 is present (`VerifiedGarbageTest/Dispatch.lean` checks it).
    "x86_64": {
        "vg_chacha20_xor_ssse3": [{"avx", "avx2"}],
        # AES-GCM-SIV's dispatchers rank `_aesni_pclmul_avx_avx2` above
        # `_aesni_avx2` and `_pclmul_avx2`, and `_vaes_vpclmul_avx512` above
        # `_vaes_avx2` and `_vpclmul_avx2`, each needing only the features of
        # the one it is above with those listed here, so never choose these
        # with them (`VerifiedGarbageTest/Dispatch.lean` checks the ranking).
        **{
            f"vg_aes_gcm_siv_{f}_{v}": [sets]
            for f in ("seal", "open")
            for v, sets in (
                ("aesni_avx2", {"pclmulqdq"}),
                ("pclmul_avx2", {"aes"}),
                ("vaes_avx2", {"pclmulqdq", "vpclmulqdq"}),
                ("vpclmul_avx2", {"aes", "vaes"}),
            )
        },
    },
}


def variants(fns):
    """`(base, suffix)` of each function that is a variant of another: the
    longest `base` it extends with `_<suffix>`, with the same signature; of
    an internal function (which has none), the longest whose suffix is the
    suffix of a variant of a function with one."""
    def find(names, ok):
        out = {}
        for name in names:
            parts = name.split("_")
            for i in range(len(parts) - 1, 1, -1):
                base = "_".join(parts[:i])
                if base in fns and fns[base][0] == fns[name][0] and ok(parts[i:]):
                    out[name] = (base, "_".join(parts[i:]))
                    break
        return out

    out = find([n for n, (sig, _) in fns.items() if sig != INTERNAL], lambda _: True)
    suffixes = {suffix for _, suffix in out.values()}

    def internal_suffix(ws):
        """A suffix of a variant of a function with a signature, or one of
        its qualified parts `<tag>_<suffix>` (`Emit.qualifiedName`), whose
        `<suffix>` is one."""
        s = "_".join(ws)
        if s in suffixes:
            return True
        return len(ws) > 1 and "_".join(ws[1:]) in suffixes and any(
            f"_{s}_" in f"_{suffix}_" for suffix in suffixes)

    out.update(find([n for n, (sig, _) in fns.items() if sig == INTERNAL], internal_suffix))
    return out


def chain(var, name):
    """The function `name` is a variant of, through every variant it is of,
    and the suffixes it adds to it, in order."""
    if name not in var:
        return name, []
    base, suffix = var[name]
    root, suffixes = chain(var, base)
    return root, suffixes + [suffix]


def qualified_extension(sufs, suffixes, suffix):
    """Whether the suffixes `sufs` are `suffixes` and one more, made of
    qualified parts `<tag>_<suffix>` (`Emit.qualifiedName`), one of which
    ends with `_<suffix>`, in any position (`sha1_avx_bmi_sha256_avx2` for
    `avx_bmi` or `avx2`)."""
    rest = list(sufs)
    for s in suffixes:
        if s not in rest:
            return False
        rest.remove(s)
    return len(rest) == 1 and f"_{suffix}_" in f"_{rest[0]}_" and rest[0] != suffix



# The Rust code outside its tests.

TOKEN = re.compile(
    r"""(?P<space>\s+)
      | (?P<comment>//[^\n]*)
      | (?P<raw>(?:br|cr|r)(?P<hashes>\#*)")
      | (?P<string>(?:b|c)?")
      | (?P<char>b?'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f_]*\}|.)|[^\\'\n])')
      | (?P<lifetime>'(?:r\#)?[A-Za-z_]\w*)
      | (?P<ident>(?:r\#)?[A-Za-z_]\w*)
      | (?P<number>[0-9]\w*)
      | (?P<punct>.)""",
    re.VERBOSE | re.DOTALL,
)

STRING_BODY = re.compile(r'(?:[^"\\]|\\.)*"', re.DOTALL)


def tokens(text):
    """The tokens of Rust source `text`, as strings, without its comments.
    String and character literals are one token each, so the braces in them
    are not mistaken for the code's."""
    out = []
    i = 0
    while i < len(text):
        if text.startswith("/*", i):
            # Block comments nest.
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            continue
        m = TOKEN.match(text, i)
        kind = m.lastgroup if m.lastgroup != "hashes" else "raw"
        if kind == "raw":
            close = '"' + m.group("hashes")
            end = text.find(close, m.end())
            end = len(text) if end < 0 else end + len(close)
            out.append(text[i:end])
            i = end
        elif kind == "string":
            body = STRING_BODY.match(text, m.end())
            end = body.end() if body else len(text)
            out.append(text[i:end])
            i = end
        else:
            if kind not in ("space", "comment"):
                out.append(m.group())
            i = m.end()
    return out


OPEN = {"(": ")", "[": "]", "{": "}"}
CLOSE = set(OPEN.values())


def group_end(toks, i):
    """The index just past the group opened by `toks[i]`."""
    depth = 0
    for j in range(i, len(toks)):
        if toks[j] in OPEN:
            depth += 1
        elif toks[j] in CLOSE:
            depth -= 1
            if depth == 0:
                return j + 1
    return len(toks)


def requires_test(toks):
    """Whether the `cfg` predicate `toks` holds only when compiling tests."""
    if toks == ["test"]:
        return True
    if len(toks) > 2 and toks[0] in ("all", "any") and toks[1] == "(":
        args, depth, cur = [], 0, []
        for t in toks[2:group_end(toks, 1) - 1]:
            if t == "," and depth == 0:
                args.append(cur)
                cur = []
                continue
            depth += t in OPEN
            depth -= t in CLOSE
            cur.append(t)
        args = [a for a in args + [cur] if a]
        if toks[0] == "all":
            return any(requires_test(a) for a in args)
        return bool(args) and all(requires_test(a) for a in args)
    return False


def attribute(toks, i):
    """`(end, inner, body)` of the attribute at `toks[i]`, if one starts there:
    the index past it, whether it is an inner attribute (`#![…]`), and the
    tokens between its brackets."""
    if toks[i] != "#":
        return None
    j = i + 1
    inner = j < len(toks) and toks[j] == "!"
    j += inner
    if j >= len(toks) or toks[j] != "[":
        return None
    end = group_end(toks, j)
    return end, inner, toks[j + 1:end - 1]


def is_test_attribute(body):
    return body == ["test"] or (
        len(body) > 3 and body[0] == "cfg" and body[1] == "(" and requires_test(body[2:-1])
    )


# The keywords starting an item that ends with `;` or a block.
ITEM = {"fn", "mod", "impl", "struct", "enum", "union", "trait", "unsafe", "extern",
        "async", "macro_rules", "default", "auto"}
# The keywords starting an item that ends with `;`, after any blocks in it.
STATEMENT = {"use", "let", "static", "type"}


def item_end(toks, i):
    """The index past the item (or statement, field, expression) at `toks[i]`."""
    j = i
    if toks[j] == "pub":
        j += 1
        if j < len(toks) and toks[j] == "(":
            j = group_end(toks, j)
    first = toks[j] if j < len(toks) else ""
    if first == "const" and j + 1 < len(toks) and toks[j + 1] in ITEM:
        first = "fn"
    statement = first in STATEMENT or first == "const"
    block = first in ITEM or first == "{" or (j + 1 < len(toks) and toks[j + 1] == "!")
    while j < len(toks):
        t = toks[j]
        if t in CLOSE:
            return j  # the end of the enclosing group
        if t == ";" or (t == "," and not (statement or block)):
            return j + 1
        if t in OPEN:
            j = group_end(toks, j)
            if t == "{" and block:
                return j
            continue
        j += 1
    return j


def mod_files(toks, path, test, nesting=()):
    """The files the `mod` declarations in `toks` of the file `path` name, with
    whether each is test-only: everything under `test`, or under an item
    gated on `test`. Inline modules nest as `nesting`."""
    base = path.parent if path.name in ("lib.rs", "main.rs", "mod.rs") else path.with_suffix("")
    out = []
    i, attr_path, gated = 0, None, False
    while i < len(toks):
        a = attribute(toks, i)
        if a:
            end, _, body = a
            if body[:2] == ["path", "="] and len(body) == 3:
                attr_path = body[2].strip('"')
            gated |= is_test_attribute(body)
            i = end
            continue
        if toks[i] == "pub" and i + 1 < len(toks) and toks[i + 1] == "(":
            i = group_end(toks, i + 1)
            continue
        if toks[i] in ("pub", "unsafe") and i + 1 < len(toks) and toks[i + 1] in ("mod", "pub"):
            i += 1
            continue
        if toks[i] == "mod" and i + 2 < len(toks):
            name, after = toks[i + 1], toks[i + 2]
            if after == ";":
                if attr_path is not None:
                    parent = base.joinpath(*nesting) if nesting else path.parent
                    files = [parent / attr_path]
                else:
                    d = base.joinpath(*nesting)
                    files = [d / f"{name}.rs", d / name / "mod.rs"]
                out += [(f, test or gated) for f in files]
            elif after == "{":
                end = group_end(toks, i + 2)
                out += mod_files(toks[i + 3:end - 1], path, test or gated, nesting + (name,))
                i = end
                attr_path, gated = None, False
                continue
        if toks[i] == "{":
            end = group_end(toks, i)
            out += mod_files(toks[i + 1:end - 1], path, test or gated, nesting)
            i = end
        else:
            i += 1
        attr_path, gated = None, False
    return out


def strip_tests(toks):
    """`toks` without its test code: the items (and statements, fields, …) an
    attribute gates on `test`, or the whole file if an inner attribute does.
    Returns `None` for a file that is all test code."""
    out = []
    i = 0
    while i < len(toks):
        a = attribute(toks, i)
        if not a:
            out.append(toks[i])
            i += 1
            continue
        end, inner, body = a
        if is_test_attribute(body):
            if inner:
                return None
            # Skip the item's other attributes, then the item.
            while end < len(toks) and attribute(toks, end):
                end = attribute(toks, end)[0]
            i = item_end(toks, end) if end < len(toks) else end
        else:
            out += toks[i:end]
            i = end
    return out


def production_rust(src):
    """The Rust code of the library's files under `src`, without its tests:
    the items gated on `test`, and the files only test code declares."""
    paths = sorted(src.rglob("*.rs"))
    toks = {p: tokens(p.read_text()) for p in paths}
    test_only = {p for p in paths if strip_tests(toks[p]) is None}
    # Files declared by test code, and those they declare in turn.
    while True:
        new = set()
        for p in paths:
            for f, test in mod_files(toks[p], p, p in test_only):
                f = pathlib.Path(f).resolve()
                if test and f in toks and f not in test_only:
                    new.add(f)
        if not new:
            break
        test_only |= new
    return "\n".join(
        " ".join(strip_tests(toks[p])) for p in paths if p not in test_only
    )

def never_with_errors(targets, feats, never_with):
    """The errors of `never_with` (`NEVER_WITH`): entries naming no function
    of their target, or one whose own features include a set it lists."""
    errors = []
    for target, entries in sorted(never_with.items()):
        fns = targets.get(target, {})
        for name, sets in sorted(entries.items()):
            if name not in fns:
                errors.append(f"{target}: NEVER_WITH names {name}, which is not a generated function")
                continue
            own = feats.get(target, {}).get(name, frozenset())
            for excluded in sets:
                if frozenset(excluded) <= own:
                    errors.append(
                        f"{target}: NEVER_WITH says {name} is never chosen with "
                        f"{', '.join(sorted(excluded))}, which it needs itself: it could never be chosen"
                    )
    return errors


def check(targets, rust, feats=None, names=None, never_with=None, disp=None, arms=None):
    """The errors of the generated functions `targets`, given the production
    Rust code `rust`, the features of each function `feats` (`features`),
    the other names of functions `names` (`all_aliases`), the
    implementations never chosen with some features (`never_with`, for the
    generated code `NEVER_WITH`) and the dispatchers `disp` (`dispatchers`),
    with their arms `arms` (`all_arms`)."""
    feats = feats or {}
    never_with = never_with or {}
    errors = never_with_errors(targets, feats, never_with)
    # The identifiers of the Rust code: `name` is one exactly when
    # `\bname\b` matches it, and a set answers without scanning the code.
    rust_words = set(re.findall(r"\w+", rust))
    for target, fns in sorted(targets.items()):
        al = (names or {}).get(target, {})
        # A use of a dispatcher is a use of each function it calls, and a use
        # of another name of a function a use of it.
        words = set(rust_words)
        for d, called_by in (disp or {}).get(target, {}).items():
            if d in words:
                words |= called_by
        words |= {canon for name, canon in al.items() if name in words}
        var = variants(fns)
        tfeats = feats.get(target, {})
        never = never_with.get(target, {})
        errors += best_callees(target, fns, var, tfeats)

        def unchosen(name, variant):
            """Whether no CPU chooses `name`'s variant for the callee's
            `variant`: one would need `name`'s features and `variant`'s, which
            include all of a set the Rust code never chooses `name`, or an
            implementation it calls, with."""
            needs = tfeats.get(name, frozenset()) | tfeats.get(variant, frozenset())
            return any(frozenset(x) <= needs for c in {name} | fns[name][1] for x in never.get(c, ()))
        by_base = {}
        for v, (base, suffix) in var.items():
            by_base.setdefault(base, []).append(suffix)
        # Each function by its root and the set of suffixes it composes.
        composed = {}
        for name in fns:
            root, suffixes = chain(var, name)
            composed.setdefault((root, tuple(sorted(suffixes))), name)
        callers = {}
        for name, (_, callees) in fns.items():
            for c in callees:
                callers.setdefault(c, set()).add(name)

        def avoided(name, callee, variant):
            """Whether a CPU with `variant`'s features runs `name` without
            `callee`: some implementation of `name` but its baseline needs no
            more features, and each that needs no more calls none of
            `callee`'s implementations (CBC encryption, whose AES-NI code
            calls no `vg_aes_encrypt_blocks` and needs no VAES)."""
            root = chain(var, name)[0]
            impls = {callee} | {f"{callee}_{s}" for s in by_base.get(callee, [])}
            limit = tfeats.get(variant, frozenset())
            runs = [
                n for n in fns
                if n != root and chain(var, n)[0] == root
                and tfeats.get(n, frozenset()) <= limit
            ]
            return bool(runs) and all(not impls & fns[n][1] for n in runs)

        tarms = (arms or {}).get(target, {})
        # BMI2 and ADX are detected only with AVX2 (crates/verified-garbage-cpu).
        implied = {"bmi2": {"avx2"}, "adx": {"avx2"}} if target in ("x86", "x86_64") else {}

        def detected(fs):
            """The features a CPU reported to have `fs` has."""
            return frozenset(fs) | frozenset().union(*(implied.get(f, set()) for f in fs))

        def chosen(dispatcher, fs):
            """What `dispatcher` runs on a CPU with exactly the features `fs`
            (and not the target an arm's `cfg!` names)."""
            tried, base = tarms[dispatcher]
            for fn, consts, extra, by_target in tried:
                needs = frozenset().union(*(tfeats.get(c, frozenset()) for c in consts)) | extra
                if not by_target and needs <= fs:
                    return fn
            return base

        def dispatched(name, callee, variant):
            """Whether the dispatcher of `name`'s function, on a CPU with
            `name`'s features and `variant`'s, runs an implementation that
            calls `variant`, one ranked before it, or none of `callee`'s
            implementations: what a variant of `name` for `variant` is for."""
            auto = chain(var, name)[0] + "_auto"
            if auto not in tarms:
                return False
            fs = detected(tfeats.get(name, frozenset()) | tfeats.get(variant, frozenset()))
            run = chosen(auto, fs)
            if run is None or run not in fns:
                return False
            impls = {callee} | {f"{callee}_{s}" for s in by_base.get(callee, [])}
            calls = impls & fns[run][1]
            if not calls or variant in calls:
                return True
            if callee + "_auto" in tarms:
                order = [fn for fn, *_ in tarms[callee + "_auto"][0]]
                return all(c in order and variant in order and order.index(c) <= order.index(variant)
                           for c in calls)
            return False

        def variants_for(name, suffix):
            """`name`'s variants for an implementation with `suffix`: the one
            adding `_<suffix>`, or those adding it qualified by a tag."""
            root, suffixes = chain(var, name)
            want = composed.get((root, tuple(sorted(suffixes + [suffix]))))
            if want is not None:
                return [want]
            return [
                n
                for (r, sufs), n in sorted(composed.items())
                if r == root and qualified_extension(sufs, suffixes, suffix)
            ]

        def unneeded(name, suffix, seen=frozenset()):
            """Whether nothing would call a variant of `name` for `suffix`: the
            Rust code does not use `name`, and every function calling it has a
            variant for `suffix` that does not (or, without one, is itself a
            function whose variant nothing would call)."""
            if name in seen or not callers.get(name) or name in words:
                return False
            for h in callers[name]:
                found = variants_for(h, suffix)
                if found:
                    if all(name in fns[v][1] for v in found):
                        return False
                elif not unneeded(h, suffix, seen | {name}):
                    return False
            return True

        for caller, (_, callees) in sorted(fns.items()):
            root, suffixes = chain(var, caller)
            for callee in sorted(callees):
                for suffix in sorted(by_base.get(callee, [])):
                    if var.get(caller, (None,))[0] == callee:
                        continue  # a variant calling its baseline
                    if suffix in suffixes:
                        continue  # already the variant
                    variant = f"{callee}_{suffix}"
                    found = variants_for(caller, suffix)
                    if not found:
                        if (
                            unneeded(caller, suffix)
                            or unchosen(caller, variant)
                            or avoided(caller, callee, variant)
                            or dispatched(caller, callee, variant)
                        ):
                            continue
                        errors.append(
                            f"{target}: {caller} calls {callee}, which has the variant "
                            f"{variant}, but there is no {caller}_{suffix} (with the same "
                            f"signature), calling {variant} or none of {callee}'s "
                            f"implementations: make {caller} generic over the "
                            f"implementations of {callee} (see CLAUDE.md)"
                        )
                    elif len(found) == 1 and callee in fns[found[0]][1]:
                        errors.append(
                            f"{target}: {found[0]}, the variant of {caller} for {variant}, "
                            f"calls the baseline {callee}: it must call {variant} (or none of "
                            f"{callee}'s implementations) instead"
                        )
                    elif all(callee in fns[name][1] for name in found):
                        errors.append(
                            f"{target}: {', '.join(found)} all call the baseline {callee}: "
                            f"the variant of {caller} for {variant} must call {variant} "
                            f"(or none of {callee}'s implementations) instead"
                        )
        called = set().union(*(c for _, c in fns.values())) if fns else set()
        called |= {canon for name, canon in al.items() if name in called}
        for name in sorted(var):
            if name not in called and name not in words:
                errors.append(
                    f"{target}: the variant {name} is neither called by another generated "
                    f"function nor used by the Rust code in src/ (outside tests): "
                    f"dispatch to it where {var[name][0]} is used, or stop emitting it"
                )
    return errors


def best_callees(target, fns, var, feats):
    """The errors of "Callers reach the best callee", for one target."""
    def need(name):
        return feats.get(name, frozenset())

    family = {}
    for name in fns:
        family.setdefault(chain(var, name)[0], []).append(name)
    errors, seen = [], set()
    for caller, (_, callees) in sorted(fns.items()):
        root = chain(var, caller)[0]
        for callee in sorted(callees):
            if callee not in fns:
                continue
            croot = chain(var, callee)[0]
            if croot == root:
                continue  # a variant calling its baseline
            for better in sorted(family[croot]):
                if not need(callee) < need(better) <= need(caller) or (root, better) in seen:
                    continue
                if any(
                    any(f in fns[h][1] and need(f) >= need(better) for f in family[croot])
                    for h in family[root]
                ):
                    continue
                seen.add((root, better))
                errors.append(
                    f"{target}: {caller} (features {', '.join(sorted(need(caller))) or 'none'}) "
                    f"calls {callee}, but no implementation of {root} calls {better}, which "
                    f"needs only features {caller} has ({', '.join(sorted(need(better)))}): "
                    f"call it from the implementation for those features"
                )
    return errors


def unread(srcs):
    """Each generated file's naked functions, other names and `_FEATURES`
    constants that `bodies`, `aliases` and `features` do not read: a change
    to how the emitter writes them must not leave them unchecked, and the
    check passing."""
    errors = []
    for target, text in srcs:
        for what, total, read in [
            ("naked functions", text.count("#[unsafe(naked)]"), sum(1 for _ in bodies(text))),
            ("other names", text.count(" use self::vg_"), len(aliases(text))),
            ("dispatchers' other names", text.count(" use crate::"), len(SOLE.findall(text))),
            ("dispatchers", text.count("\npub unsafe fn vg_"), len(DISPATCHER.findall(text))),
            ("_FEATURES constants", text.count("_FEATURES: "), len(FEATURES.findall(text))),
        ]:
            if read < total:
                errors.append(f"{target}: read {read} of the {total} {what} of a generated file")
    return errors


def main():
    srcs = sources()
    errors = unread(srcs) + check(
        functions(srcs), production_rust(ROOT / "src"), features(srcs), all_aliases(srcs), NEVER_WITH,
        disp=dispatchers(srcs), arms=all_arms(srcs)
    )
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print("variants reach every caller, and every variant is used")
    return 0


if __name__ == "__main__":
    sys.exit(main())
