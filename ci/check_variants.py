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
  call, but not their `_x2_sha3` variants). Variants compose: a variant
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

An *internal function* (`Rust.Internal` in `lean/VerifiedGarbage/TCB/Rust.lean`),
which the emitter writes to `src/internal/<name>.rs` of its crate, is code
that verified functions call but that has no contract: it has no Rust
signature (`fn <name>()`), so its variants are not found by their
signature. A variant of an internal function `f` is the internal function
`f_<suffix>` whose suffix is made of words that are the words of the
suffixes of variants of functions with signatures on the target (`_shani`,
`_avx2`, `_blake2b_avx2`, …): `vg_p384_mul_mod_n` is not a variant of
`vg_p384_mul`, as no function of a signature has a variant `_mod_n`. Its
CPU features are in a `_FEATURES` constant of its file, as an artifact's.

A function the emitter renders as another name of an identical function of
its module (`pub use self::<f> as <name>;`, `Rust.alias` in
`lean/VerifiedGarbage/TCB/Rust.lean`) is that function's code: it has its
signature and callees, and a use of it is a use of that function.

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
    """Each generated file's target and text: its modules' and its internal
    functions' (`internal/<name>.rs`)."""
    return [(target, path.read_text())
            for target, d in asm_layout.target_dirs(ROOT).items()
            for path in sorted(d.glob("*.rs")) + sorted(d.glob("internal/vg_*.rs"))]


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
    the name it gives it: `{name: function}`."""
    return {m.group(2): m.group(1) for m in ALIAS.finditer(text)}


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


def variants(fns):
    """`(base, suffix)` of each function that is a variant of another: the
    longest `base` it extends with `_<suffix>`, with the same signature; of
    an internal function (which has none), the longest whose suffix is made
    of the words of the suffixes of the variants of functions with one."""
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
    words = {w for _, suffix in out.values() for w in suffix.split("_")}
    out.update(find([n for n, (sig, _) in fns.items() if sig == INTERNAL],
                    lambda ws: all(w in words for w in ws)))
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

def check(targets, rust, feats=None, names=None):
    """The errors of the generated functions `targets`, given the production
    Rust code `rust`, the features of each function `feats` (`features`) and
    the other names of functions `names` (`all_aliases`)."""
    errors = []
    # The identifiers of the Rust code: `name` is one exactly when
    # `\bname\b` matches it, and a set answers without scanning the code.
    words = set(re.findall(r"\w+", rust))
    for target, fns in sorted(targets.items()):
        al = (names or {}).get(target, {})
        # A use of another name of a function is a use of it.
        words |= {canon for name, canon in al.items() if name in words}
        var = variants(fns)
        errors += best_callees(target, fns, var, (feats or {}).get(target, {}))
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
            ("_FEATURES constants", text.count("_FEATURES: "), len(FEATURES.findall(text))),
        ]:
            if read < total:
                errors.append(f"{target}: read {read} of the {total} {what} of a generated file")
    return errors


def main():
    srcs = sources()
    errors = unread(srcs) + check(
        functions(srcs), production_rust(ROOT / "src"), features(srcs), all_aliases(srcs)
    )
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print("variants reach every caller, and every variant is used")
    return 0


if __name__ == "__main__":
    sys.exit(main())
