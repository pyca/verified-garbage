#!/usr/bin/env python3
"""Checks that every implementation of a verified function reaches every
function built on it, from the generated code in `src/asm/`.

A primitive can have several implementations with the same contract, e.g.
`vg_sha256_compress` and `vg_sha256_compress_shani`: a *variant* of a
function `f` on a target is a function of that target named `f_<suffix>`
with the same Rust signature (`_shani`, `_avx2`, …).

* **Variants flow to callers.** If a function `g` calls `f`, and `f` has a
  variant `f_<s>`, then `g` must have the variant `g_<s>`, and `g_<s>` must
  not call the baseline `f`: it calls `f_<s>`, or none of `f`'s
  implementations, when it does the work itself (e.g. ML-KEM's AArch64
  `vg_mlkem768_keygen_sha3`, which runs two Keccak permutations at once
  with `vg_keccak_f1600_x2_sha3` rather than calling the sponge functions
  `vg_keccak_absorb_scratch_sha3`, … that `vg_mlkem768_keygen` calls the
  baseline of). (A variant may call the function it is a variant of, e.g.
  for a tail it leaves to the baseline code.) A function whose variant
  nothing would call needs none: one the Rust code does not use, all of
  whose callers have variants for `f_<s>` that do not call it, or need
  none themselves (`vg_mlkem_sample_ntt`, which `vg_mlkem768_keygen`, …
  call, but not their `_sha3` variants). Variants compose: a variant
  of a variant, `g_<t>_<s>`, has both suffixes, in either order, so when
  `g_<t>` calls `f`, its variant for `f_<s>` may be `g_<t>_<s>` or
  `g_<s>_<t>` (e.g. Ed25519's operations over each SHA-512 backend and each
  field multiplication: `vg_ed25519_verify_avx2_adx` is the variant both of
  `vg_ed25519_verify_avx2` for `vg_ed25519_verify_equation_adx` and of
  `vg_ed25519_verify_adx` for `vg_sha512_update_avx2`).
  A caller that takes the choice among several functions as an argument
  (e.g. RSA-OAEP's, calling the hash function its argument names) has
  variants by *tiers* instead: each variant calls one implementation of
  each function, the fastest its CPU features allow. Its variants then need
  not have the names above: a variant `f_<s>` of a function `f` they call
  reaches them if one of the caller's variants calls it, and none of them
  that calls the baseline `f` has every CPU feature `f_<s>` needs (its
  `<NAME>_FEATURES`, in the generated code), so no CPU that could run
  `f_<s>` runs a variant calling the baseline.
  A caller generic over several interfaces qualifies each suffix with a tag
  for its interface (`Emit.qualifiedName` in `lean/VerifiedGarbage/TCB/Emit.lean`),
  since two interfaces may have variants with the same suffix: its variant
  for `f_<s>` may add `<tag>_<s>` instead (`vg_argon2_g_avx512`, the
  variant of `vg_argon2` for `vg_argon2_compress_avx512`), and one of its
  variants adding a part ending in `_<s>` must not call `f`.
* **Every variant is used.** Each variant is called by another generated
  function or used by the Rust code of the crate (`src/`, outside
  `src/asm/`), not counting its tests: the generated modules allow dead
  code, so a variant the Rust dispatch forgot would otherwise go unnoticed,
  and a variant only a test calls is one nothing else runs. Test code is
  every item gated by a `cfg` that requires `test` (`#[cfg(test)]`,
  `#[cfg(all(test, …))]`, an inner `#![cfg(test)]`) or marked `#[test]`,
  and every file such a `mod` declaration names, with the files it
  declares in turn. (Code a macro expands only in its tests, from an
  argument passed outside them, is not found: name such functions only in
  the test.)

See "An optimized implementation reaches everything built on it" in
CLAUDE.md.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ASM = ROOT / "src" / "asm"

FN = re.compile(
    r"^pub\(crate\) unsafe extern \"[\w-]+\" fn (vg_\w+)\((.*?)\)(?: -> ([^{]+?))? \{\n(.*?)^\}",
    re.MULTILINE | re.DOTALL,
)
SYM = re.compile(r"\w+ = sym (?:\w+::)*(vg_\w+)")
FEATURES = re.compile(
    r"^pub\(crate\) const (VG_\w+)_FEATURES: crate::cpu::Features = "
    r"crate::cpu::Features::of\(&\[(.*?)\]\);",
    re.MULTILINE,
)


def functions():
    """For each target, each generated function's signature and callees."""
    targets = {}
    for path in sorted(ASM.glob("*/*.rs")):
        fns = targets.setdefault(path.parent.name, {})
        for m in FN.finditer(path.read_text()):
            name, params, ret, body = m.groups()
            fns[name] = ((params, (ret or "").strip()), set(SYM.findall(body)))
    return targets


def features():
    """For each target, the CPU features each generated function needs that
    the target's baseline does not (none for most)."""
    targets = {}
    for path in sorted(ASM.glob("*/*.rs")):
        feats = targets.setdefault(path.parent.name, {})
        for m in FEATURES.finditer(path.read_text()):
            feats[m.group(1).lower()] = frozenset(re.findall(r'"(\w+)"', m.group(2)))
    return targets


def variants(fns):
    """`(base, suffix)` of each function that is a variant of another: the
    longest `base` it extends with `_<suffix>`, with the same signature."""
    out = {}
    for name, (sig, _) in fns.items():
        parts = name.split("_")
        for i in range(len(parts) - 1, 1, -1):
            base = "_".join(parts[:i])
            if base in fns and fns[base][0] == sig:
                out[name] = (base, "_".join(parts[i:]))
                break
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
    """Whether the suffixes `sufs` are `suffixes` and one more, `<tag>_<suffix>`."""
    rest = list(sufs)
    for s in suffixes:
        if s not in rest:
            return False
        rest.remove(s)
    return len(rest) == 1 and rest[0].endswith("_" + suffix)



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
    """The Rust code of the crate's files under `src` (outside `src/asm/`),
    without its tests: the items gated on `test`, and the files only test code
    declares."""
    paths = sorted(p for p in src.rglob("*.rs") if src / "asm" not in p.parents and p != src / "asm")
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

def check(targets, rust, feats=None):
    errors = []
    for target, fns in sorted(targets.items()):
        feat = (feats or {}).get(target, {})
        var = variants(fns)
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

        def tiered(caller, callee, variant):
            """Whether the variants of `caller` choose `callee`'s implementation
            by tiers of CPU features: one of them calls `variant`, and none
            that calls the baseline `callee` has every feature `variant`
            needs."""
            need = feat.get(variant, frozenset())
            root = chain(var, caller)[0]
            family = [n for n in fns if chain(var, n)[0] == root]
            return bool(need) and any(variant in fns[n][1] for n in family) and all(
                not need <= feat.get(n, frozenset()) for n in family if callee in fns[n][1]
            )

        def unneeded(name, suffix, seen=frozenset()):
            """Whether nothing would call a variant of `name` for `suffix`: the
            Rust code does not use `name`, and every function calling it has a
            variant for `suffix` that does not (or, without one, is itself a
            function whose variant nothing would call)."""
            if name in seen or not callers.get(name) or re.search(rf"\b{name}\b", rust):
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
                    if tiered(caller, callee, variant):
                        continue
                    if not found:
                        if unneeded(caller, suffix):
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
        for name in sorted(var):
            if name not in called and not re.search(rf"\b{name}\b", rust):
                errors.append(
                    f"{target}: the variant {name} is neither called by another generated "
                    f"function nor used by the Rust code in src/ (outside src/asm/ and tests): "
                    f"dispatch to it where {var[name][0]} is used, or stop emitting it"
                )
    return errors


def main():
    errors = check(functions(), production_rust(ROOT / "src"), features())
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print("variants reach every caller, and every variant is used")
    return 0


if __name__ == "__main__":
    sys.exit(main())
