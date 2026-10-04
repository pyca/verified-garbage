#!/usr/bin/env python3
"""Checks that every implementation of a verified function reaches every
function built on it, from the generated code in `src/asm/`.

A primitive can have several implementations with the same contract, e.g.
`vg_sha256_compress` and `vg_sha256_compress_shani`: a *variant* of a
function `f` on a target is a function of that target named `f_<suffix>`
with the same Rust signature (`_shani`, `_avx2`, …).

* **Variants flow to callers.** If a function `g` calls `f`, and `f` has a
  variant `f_<s>`, then `g` must have the variant `g_<s>`, and it must call
  `f_<s>`. (A variant may call the function it is a variant of, e.g. for a
  tail it leaves to the baseline code.) Variants compose: a variant of a
  variant, `g_<t>_<s>`, has both suffixes, in either order, so when `g_<t>`
  calls `f`, its variant for `f_<s>` may be `g_<t>_<s>` or `g_<s>_<t>`
  (e.g. Ed25519's operations over each SHA-512 backend and each field
  multiplication: `vg_ed25519_verify_avx2_adx` is the variant both of
  `vg_ed25519_verify_avx2` for `vg_ed25519_verify_equation_adx` and of
  `vg_ed25519_verify_adx` for `vg_sha512_update_avx2`).
  A caller generic over several interfaces qualifies each suffix with a tag
  for its interface (`Emit.qualifiedName` in `lean/VerifiedGarbage/TCB/Emit.lean`),
  since two interfaces may have variants with the same suffix: its variant
  for `f_<s>` may add `<tag>_<s>` instead (`vg_argon2_g_avx512`, the
  variant of `vg_argon2` for `vg_argon2_compress_avx512`), and one of its
  variants adding a part ending in `_<s>` must call `f_<s>`.
* **Every variant is used.** Each variant is called by another generated
  function or used by the Rust code of the crate (`src/`, outside
  `src/asm/`): the generated modules allow dead code, so a variant the Rust
  dispatch forgot would otherwise go unnoticed.

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
COMMENT = re.compile(r"//.*$", re.MULTILINE)


def functions():
    """For each target, each generated function's signature and callees."""
    targets = {}
    for path in sorted(ASM.glob("*/*.rs")):
        fns = targets.setdefault(path.parent.name, {})
        for m in FN.finditer(path.read_text()):
            name, params, ret, body = m.groups()
            fns[name] = ((params, (ret or "").strip()), set(SYM.findall(body)))
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


def check(targets, rust):
    errors = []
    for target, fns in sorted(targets.items()):
        var = variants(fns)
        by_base = {}
        for v, (base, suffix) in var.items():
            by_base.setdefault(base, []).append(suffix)
        # Each function by its root and the set of suffixes it composes.
        composed = {}
        for name in fns:
            root, suffixes = chain(var, name)
            composed.setdefault((root, tuple(sorted(suffixes))), name)
        for caller, (_, callees) in sorted(fns.items()):
            root, suffixes = chain(var, caller)
            for callee in sorted(callees):
                for suffix in sorted(by_base.get(callee, [])):
                    if var.get(caller, (None,))[0] == callee:
                        continue  # a variant calling its baseline
                    if suffix in suffixes:
                        continue  # already the variant
                    variant = f"{callee}_{suffix}"
                    want = composed.get((root, tuple(sorted(suffixes + [suffix]))))
                    if want is None:
                        # The variants adding the suffix qualified by a tag.
                        tagged = [
                            name
                            for (r, sufs), name in sorted(composed.items())
                            if r == root and qualified_extension(sufs, suffixes, suffix)
                        ]
                        if not tagged:
                            errors.append(
                                f"{target}: {caller} calls {callee}, which has the variant "
                                f"{variant}, but there is no {caller}_{suffix} (with the same "
                                f"signature) calling it: make {caller} generic over the "
                                f"implementations of {callee} (see CLAUDE.md)"
                            )
                        elif not any(variant in fns[name][1] for name in tagged):
                            errors.append(
                                f"{target}: none of {', '.join(tagged)} calls {variant}"
                            )
                    elif variant not in fns[want][1]:
                        errors.append(f"{target}: {want} does not call {variant}")
        called = set().union(*(c for _, c in fns.values())) if fns else set()
        for name in sorted(var):
            if name not in called and not re.search(rf"\b{name}\b", rust):
                errors.append(
                    f"{target}: the variant {name} is neither called by another generated "
                    f"function nor used by the Rust code in src/ (outside src/asm/): dispatch "
                    f"to it where {var[name][0]} is used"
                )
    return errors


def main():
    # The crate's Rust code, without comments (which may name a function
    # without using it).
    rust = "".join(
        COMMENT.sub("", p.read_text())
        for p in sorted((ROOT / "src").rglob("*.rs"))
        if ASM not in p.parents
    )
    errors = check(functions(), rust)
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print("variants reach every caller, and every variant is used")
    return 0


if __name__ == "__main__":
    sys.exit(main())
