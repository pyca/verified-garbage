#!/usr/bin/env python3
"""Checks that the code a CPU runs calls the best implementation of each
function it calls, from the generated code, each target's
`crates/verified-garbage-asm-<target>/src/`.

A primitive can have several implementations with the same contract, e.g.
`vg_sha256_compress` and `vg_sha256_compress_shani`: a *variant* of a
function `f` on a target is a function of that target named `f_<suffix>`
with the same Rust signature (`_shani`, `_avx2`, …). Each function has a
generated *dispatcher*, `f_auto` (`Rust.dispatcher` in
`lean/VerifiedGarbage/TCB/Rust.lean`), which tries its implementations in
the order `VG.Dispatch.ranking` gives them and runs the first the CPU has
the features of: the choice is made there, not in Rust.

* **Callers run the best callee.** For each dispatcher, on a CPU with the
  features of each implementation it can choose (and with those and the
  features of each variant of a function that implementation calls,
  directly or through others), the implementation the dispatcher runs, and
  each function it calls in turn, calls the implementation of each of its
  callees that the callee's dispatcher would choose on that CPU, or one that
  dispatcher tries before it. A callee with no dispatcher (an internal
  function, `Rust.Internal`) has no ranking: there the implementation
  called must need no fewer features than any other the CPU can run. This
  is what makes every function that calls a function with variants generic
  over them (CLAUDE.md, "An optimized implementation reaches everything
  built on it"): without its variant, a caller would run the baseline
  callee on a CPU that has a better one. A CPU has what CPU detection
  reports with the features it has (`IMPLIED`: on x86, AVX with AVX2,
  AVX-512, SHA512, VAES or VPCLMULQDQ, and AVX2 with BMI2 or ADX); a
  dispatcher's arm whose condition depends on the compilation target
  (`cfg!`) is not taken.
* **Every variant is reached.** Each variant is tried by a dispatcher,
  named in a table of functions (`Artifact.tables`), called by another
  generated function, or named by the Rust code in `src/`: one that none of
  these reaches is code no CPU runs (a combination of variants that each CPU
  able to run it runs another one ranked before, which its dispatcher
  leaves out), so stop emitting it.

An *internal function*, which the emitter writes to `src/internal/<name>.rs`
of its crate, is code that verified functions call but that has no
contract: it has no Rust signature (`fn <name>()`). A variant of an
internal function `f` is the internal function `f_<suffix>` whose suffix is
the suffix of a variant of a function with a signature on the target, or a
qualified part `_<tag>_<suffix>` of one whose `<suffix>` is one (`_shani`,
`_avx2`, `_sha1_avx_bmi` of `_sha1_avx_bmi_sha256_avx2`), each variant of a
variant adding one: `vg_p384_mul_mod_n` is not a variant of `vg_p384_mul`,
as no function of a signature has a variant `_mod_n`, nor
`vg_keccak_f1600_x2` of `vg_keccak_f1600` (though ML-KEM's have `_x2_sha3`).
Its CPU features are in a `_FEATURES` constant of its file, as an
artifact's.

A function the emitter renders as another name of an identical function of
its module (`pub use self::<f> as <name>;`, `Rust.alias`) is that
function's code.

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
# A dispatcher (`Rust.dispatcher`), to the end of its body.
DISPATCHER = re.compile(r"^pub unsafe fn (vg_\w+)\(.*?^\}\n", re.MULTILINE | re.DOTALL)
# An arm of a dispatcher: its condition and the function it returns.
ARM = re.compile(
    r"if (?P<cond>[^\n]*\bcpu\b[^\n]*) \{\n(?:\s*//[^\n]*\n)*"
    r"\s*return unsafe \{ crate::\w+::(?P<fn>vg_\w+)\(")
# A dispatcher's last call, of its base.
BASE_CALL = re.compile(r"\n    unsafe \{ crate::\w+::(vg_\w+)\(")
# A function a table of functions names (`Artifact.tables`).
TABLE_FN = re.compile(r"crate::(?:\w+::)+(vg_\w+) as \*const \(\)")
# `<operand> = sym <path>`, found from the literal ` = sym ` (a leading
# `\w+` would be tried at every word character of the code: 30 times slower).
SYM = re.compile(r" = sym (?:\w+::)*(vg_\w+)")
WORD = re.compile(r"\w")
FEATURES = re.compile(
    r"^pub(?:\(crate\))? const (VG_\w+)_FEATURES: (?:crate::cpu|verified_garbage_cpu)::Features = "
    r"(?:crate::cpu|verified_garbage_cpu)::Features\((.*?)\);",
    re.MULTILINE,
)

# The ranking of the implementations of an internal function
# (`Rust.internalRanking`), and each of its rows.
RANKING = re.compile(
    r"^pub\(crate\) const (VG_\w+)_RANKING: [^\n]*= &\[\n(.*?)^\];", re.MULTILINE | re.DOTALL)
RANK_MODULE = re.compile(r'^    \("(\w+)", &\[\n(.*?)^    \]\),$', re.MULTILINE | re.DOTALL)
# The module of a file of dispatchers (`Rust.dispatchFile`).
DISPATCH_MODULE = re.compile(r"^//! The dispatchers of the verified `(\w+)` functions", re.MULTILINE)
RANK_ROW = re.compile(
    r'\("(vg_\w+)", (?:crate::cpu|verified_garbage_cpu)::Features\(([^)]*)\), &\[([^\]]*)\]\)')

# The signature of an internal function (`fn <name>()`).
INTERNAL = ("", "")

# For each target, the features CPU detection reports each feature only with
# (`decode` in `crates/verified-garbage-cpu/src/detect.rs`).
_AVX = {"avx"}
IMPLIED = {t: {"avx2": _AVX, "bmi2": {"avx", "avx2"}, "adx": {"avx", "avx2"},
               "avx512f": {"avx", "avx2"}, "aes": {"ssse3"}, "sha512": _AVX,
               "avx512ifma": {"avx", "avx2", "avx512f", "avx512vl"}, "avx512vl": _AVX, "vaes": {"avx", "aes", "ssse3"},
               "vpclmulqdq": _AVX, "avx512bw": _AVX}
           for t in ("x86", "x86_64")}


def sources():
    """Each generated file's target and text: its modules', its internal
    functions' (`internal/<name>.rs`), its dispatchers' (`dispatch/<module>.rs`)
    and its tables' of functions (`fn_tables/<name>.rs`)."""
    return [(target, path.read_text())
            for target, d in asm_layout.target_dirs(ROOT).items()
            for path in sorted(d.glob("*.rs")) + sorted(d.glob("internal/vg_*.rs"))
            + sorted(d.glob("dispatch/*.rs")) + sorted(d.glob("fn_tables/*.rs"))]


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


def aliases(text):
    """Each other name of a function of a generated file (`Rust.alias`), by
    the name it gives it: `{name: function}`; not a dispatcher's."""
    return {m.group(2): m.group(1) for m in ALIAS.finditer(text)}


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


def file_arms(text):
    """Each dispatcher of a generated file as the implementations it tries,
    in order, each with the `_FEATURES` constants and the other features
    its condition names (`*` for any, `cpu.0 != 0`) and whether it depends
    on the compilation target (`cfg!`), then its base: `{name: ([(function, {constant, …}, {feature,
    …}, by_target), …], base)}`; a dispatcher of one implementation
    (`Rust.soleDispatcher`) tries none."""
    out = {}
    for m in DISPATCHER.finditer(text):
        body = m.group(0)
        tried = [(a.group("fn"),
                  {c.lower() for c in re.findall(r"(VG_\w+)_FEATURES", a.group("cond"))},
                  {f.lower() for f in re.findall(r"feature::(\w+)", a.group("cond"))}
                  | ({"*"} if "cpu.0 != 0" in a.group("cond") else set()),
                  "cfg!(" in a.group("cond"))
                 for a in ARM.finditer(body)]
        base = BASE_CALL.findall(body)
        out[m.group(1)] = (tried, base[-1] if base else None)
    out.update({m.group(2): ([], m.group(1)) for m in SOLE.finditer(text)})
    for m in RANKING.finditer(text):
        for mod, rows in RANK_MODULE.findall(m.group(2)):
            tried = []
            for fn, bits, vendors in RANK_ROW.findall(rows):
                fs = {f.lower() for f in re.findall(r"feature::(\w+)", bits)}
                tried.append((fn, set(), fs or {"*"}, bool(vendors.strip())))
            out[f"{INTERNAL_RANK}{mod}:{m.group(1).lower()}"] = (tried, m.group(1).lower())
    mod = DISPATCH_MODULE.search(text)
    for name in list(out):
        if not name.startswith(INTERNAL_RANK):
            DISPATCHER_MODULE[name] = mod.group(1) if mod else None
    return out


# The module of each dispatcher's file, by its name (`file_arms` fills it).
DISPATCHER_MODULE = {}


# The key of an internal function's ranking among the dispatchers' (`file_arms`).
INTERNAL_RANK = "ranking:"


def table_functions(text):
    """The functions a generated file's tables of functions name."""
    return set(TABLE_FN.findall(text))


def features(srcs):
    """For each target, the CPU features each generated function (and
    table) needs, by its name (those that need none are left out)."""
    targets = {}
    for target, text in srcs:
        feats = targets.setdefault(target, {})
        for m in FEATURES.finditer(text):
            feats[m.group(1).lower()] = frozenset(
                f.lower() for f in re.findall(r"(?:crate::cpu|verified_garbage_cpu)::feature::(\w+)", m.group(2)))
    return targets


def per_target(srcs, read):
    """For each target, what `read` gives of each of its files, together."""
    targets = {}
    for target, text in srcs:
        got = read(text)
        if isinstance(got, set):
            targets.setdefault(target, set()).update(got)
        else:
            targets.setdefault(target, {}).update(got)
    return targets


def variants(fns):
    """`(base, suffix)` of each function that is a variant of another: the
    longest `base` it extends with `_<suffix>`, with the same signature; of
    an internal function (which has none), the longest whose suffix is the
    suffix of a variant of a function with one, or a qualified part of one."""
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
        s = "_".join(ws)
        if s in suffixes:
            return True
        return len(ws) > 1 and "_".join(ws[1:]) in suffixes and any(
            f"_{s}_" in f"_{suffix}_" for suffix in suffixes)

    out.update(find([n for n, (sig, _) in fns.items() if sig == INTERNAL], internal_suffix))
    return out


def root_of(var, name):
    """The function `name` is a variant of, through every variant it is of."""
    while name in var:
        name = var[name][0]
    return name


def check(targets, rust, feats=None, arms=None, tables=None):
    """The errors of the generated functions `targets`, given the Rust code
    `rust`, the features of each function `feats` (`features`), the
    dispatchers' `arms` (`file_arms`) and the functions tables name
    (`table_functions`)."""
    feats = feats or {}
    rust_words = set(re.findall(r"\w+", rust))
    errors = []
    for target, fns in sorted(targets.items()):
        tfeats = feats.get(target, {})
        tarms = (arms or {}).get(target, {})
        implied = IMPLIED.get(target, {})
        var = variants(fns)
        root = {n: root_of(var, n) for n in fns}
        family = {}
        for n, r in root.items():
            family.setdefault(r, set()).add(n)

        def detected(fs):
            """The features a CPU reported to have `fs` has."""
            return frozenset(fs).union(*(implied.get(f, ()) for f in fs))

        def needs(name, consts=(), extra=()):
            """The features `name` needs, or an arm of its with `consts`'s and `extra`."""
            return detected(tfeats.get(name, frozenset()).union(
                *(tfeats.get(c, frozenset()) for c in consts), extra))

        def ranking_of(r, module):
            """The key in `tarms` of the dispatcher of the function `r`, or of
            its ranking as an internal function called by `module`'s."""
            for k in (r + "_auto", f"{INTERNAL_RANK}{module}:{r}"):
                if k in tarms:
                    return k
            return None

        def order(auto):
            """What `auto` tries, then its base, or `None` without one."""
            if auto not in tarms:
                return None
            tried, base = tarms[auto]
            return [fn for fn, *_ in tried] + [base]

        def chosen(auto, fs):
            """What the dispatcher `auto` runs on a CPU with the features `fs`."""
            tried, base = tarms[auto]
            for fn, consts, extra, by_target in tried:
                if not by_target and needs(fn, consts, extra - {"*"}) <= fs and (
                        "*" not in extra or fs):
                    return fn
            return base

        def closure(name):
            """`name` and every function it calls, directly or through others."""
            seen, todo = set(), [name]
            while todo:
                n = todo.pop()
                if n in seen or n not in fns:
                    continue
                seen.add(n)
                todo += fns[n][1]
            return seen

        # The suffixes the ranking chooses by the compilation target, whose
        # implementations are not better elsewhere.
        by_target_suffixes = set()
        for tried, _ in tarms.values():
            for fn, _, _, by_target in tried:
                if by_target and fn in var:
                    n = fn
                    while n in var:
                        by_target_suffixes |= set(var[n][1].split("_"))
                        n = var[n][0]

        def by_target(name):
            """Whether a suffix `name` adds is one the ranking chooses by target."""
            n = name
            while n in var:
                if set(var[n][1].split("_")) & by_target_suffixes:
                    return True
                n = var[n][0]
            return False

        reported = set()
        for auto, (tried, base) in sorted(tarms.items()):
            if auto.startswith(INTERNAL_RANK):
                continue
            impls = [(fn, needs(fn, consts, extra - {"*"})) for fn, consts, extra, by_target in tried
                     if not by_target] + [(base, needs(base))]
            sets = set()
            for g, fg in impls:
                if g not in fns:
                    continue
                sets.add(fg)
                for n in closure(g):
                    for v in family[root[n]]:
                        sets.add(detected(fg | needs(v)))
            for fs in sorted(sets, key=sorted):
                start = chosen(auto, fs)
                seen, todo = set(), [(start, (start,))]
                while todo:
                    x, path = todo.pop()
                    if x in seen or x not in fns:
                        continue
                    seen.add(x)
                    calls = {}
                    for c in fns[x][1]:
                        if c in fns:
                            calls.setdefault(root[c], set()).add(c)
                    for r, cs in sorted(calls.items()):
                        if r == root[x]:
                            # Another implementation of its own function (for a
                            # tail): not the code a dispatcher chose.
                            continue
                        k = ranking_of(r, DISPATCHER_MODULE.get(auto))
                        if k is None or len(family[r]) == 1:
                            todo += [(c, path + (c,)) for c in sorted(cs)]
                            continue
                        ranked = order(k)
                        b = chosen(k, fs)
                        good = [c for c in sorted(cs)
                                if c in ranked and ranked.index(c) <= ranked.index(b)]
                        # Only the best is the code the CPU runs for it: one
                        # ranked below is for some inputs (a short one, say).
                        todo += [(c, path + (c,)) for c in good]
                        if good or (x, r, b) in reported:
                            continue
                        # The dispatcher may rank lower an implementation that
                        # calls it: then the ranking chose, and none is missing.
                        if any(needs(y, consts, extra - {"*"}) <= fs and any(
                                c in ranked and ranked.index(c) <= ranked.index(b)
                                for c in closure(y) if root.get(c) == r)
                               for y, consts, extra, _ in tried + [(base, (), set(), False)]):
                            continue
                        reported.add((x, r, b))
                        errors.append(
                            f"{target}: on a CPU with {', '.join(sorted(fs)) or 'no feature'}, "
                            f"{auto} runs {' -> '.join(path)}, which calls {', '.join(sorted(cs))}, "
                            f"but {b} runs there and is better: make {x}'s function generic over "
                            f"the implementations of {r} (see CLAUDE.md)")

        reached = set(tables.get(target, set())) if tables else set()
        reached |= {n for n in fns if n in rust_words}
        for auto in tarms:
            if not auto.startswith(INTERNAL_RANK):
                reached |= set(order(auto))
        todo = list(reached)
        while todo:
            n = todo.pop()
            for c in fns.get(n, ((), ()))[1]:
                if c not in reached:
                    reached.add(c)
                    todo.append(c)
        for name in sorted(var):
            if name not in reached:
                errors.append(
                    f"{target}: no dispatcher, table, generated function or Rust code reaches "
                    f"the variant {name}: no CPU runs it, so stop emitting it")
    return errors


def unread(srcs):
    """Each generated file's naked functions, other names, dispatchers and
    `_FEATURES` constants that `bodies`, `aliases`, `file_arms` and
    `features` do not read: a change to how the emitter writes them must not
    leave them unchecked, and the check passing."""
    errors = []
    for target, text in srcs:
        for what, total, read in [
            ("naked functions", text.count("#[unsafe(naked)]"), sum(1 for _ in bodies(text))),
            ("other names", text.count(" use self::vg_"), len(aliases(text))),
            ("dispatchers' other names", text.count(" use crate::"), len(SOLE.findall(text))),
            ("dispatchers", text.count("\npub unsafe fn vg_"), len(DISPATCHER.findall(text))),
            ("dispatchers' arms", text.count("return unsafe { crate::"),
             sum(len(t) for t, _ in file_arms(text).values())),
            ("_FEATURES constants", text.count("_FEATURES: "), len(FEATURES.findall(text))),
        ]:
            if read < total:
                errors.append(f"{target}: read {read} of the {total} {what} of a generated file")
    return errors


def main():
    srcs = sources()
    rust = "\n".join(p.read_text() for p in sorted((ROOT / "src").rglob("*.rs")))
    errors = unread(srcs) + check(
        functions(srcs), rust, features(srcs), per_target(srcs, file_arms),
        per_target(srcs, table_functions))
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print("every caller runs the best callee, and every variant is reached")
    return 0


if __name__ == "__main__":
    sys.exit(main())
