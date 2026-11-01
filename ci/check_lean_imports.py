#!/usr/bin/env python3
"""Checks the import discipline between the directories of
lean/VerifiedGarbage/, which keeps the trusted base small and separate from
proofs. Exits non-zero on violations.

  * TCB/   imports only Lean core and TCB/  (no Mathlib: smaller trusted base).
  * Spec/  imports only TCB/, Spec/ and Mathlib.
  * Impl/  imports only TCB/, Spec/, Impl/, Mathlib and Lean core's
    elaborator (`Lean.Elab`, for term elaborators that build tables:
    `Impl/NatPairs.lean`), never proofs.
  * A module of a target (one with a directory of TCB/, e.g. `Arm`, as a
    component of its path) imports no module of another target: a change
    to one target would rebuild the other's modules too, and a CI shard
    (ci/lean_shards.py), which builds a module with everything it imports,
    would check both. What more than one target uses goes in a
    target-independent module.
  * TCB/   holds definitions only: no `theorem` or `lemma` (CLAUDE.md), so
    that what is trusted is what is reviewed as trusted; lemmas about it go
    in Proof/.
  * TCB/'s precompiled libraries (lakefile.toml) are one per target,
    `NativeTCB<Target>` (its `libName` `VerifiedGarbage_NativeTCB<Target>`,
    which the emitter loads), and `NativeTCB` for the rest, each module in
    exactly one; and a change to a target's TCB/ rebuilds no module of
    another target and no native module of another library
    (ci/lean_shards.py's traces). A native module depends on the whole
    shared library of each other library it imports from, so with one
    library for TCB/, adding an instruction to one ISA rebuilt every
    native spec, tactic and target. The audit records' modules
    (`AUDIT_RECORDS`) are the exception: they are `NativeAuditRecords`, which
    every other library loads as a plugin.
"""

import pathlib
import re
import sys
import tomllib

import lean_shards
from check_registrations import THEOREM, code_only

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean" / "VerifiedGarbage"

# An import, matched at the start of a line: `import`, and in a module
# `public`, `meta` and `all` imports, with no part of it on another line.
IMPORT_ANY = re.compile(r"[^\S\n]*(?:public[^\S\n]+)?(?:meta[^\S\n]+)?import[^\S\n]+(?:all[^\S\n]+)?(\S+)")

ALLOWED_IMPORTS = {
    "TCB": ("Lean", "VerifiedGarbage.TCB."),
    "Spec": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "Mathlib"),
    "Impl": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "VerifiedGarbage.Impl.", "Mathlib",
             "Lean.Elab"),
}


def allowed(mod: str, prefixes: tuple[str, ...]) -> bool:
    return any(mod == p or mod.startswith(p if p.endswith(".") else p + ".") for p in prefixes)


def target_of(parts, targets: set[str]) -> str | None:
    return next((p for p in parts if p in targets), None)


def tcb_lemmas(lean: pathlib.Path, texts: dict[pathlib.Path, str] | None = None) -> list[str]:
    """A line for each theorem or lemma under `lean`'s (lean/VerifiedGarbage/'s)
    TCB/, outside comments and strings (from `texts`, each file's, if given)."""
    out = []
    for f in sorted((lean / "TCB").rglob("*.lean")):
        code = code_only(texts[f] if texts else f.read_text())
        for m in THEOREM.finditer(code):
            line = code.count("\n", 0, m.start()) + 1
            out.append(f"{f.relative_to(lean.parent.parent)}:{line}: a {m.group(1)} in TCB/, "
                       "which holds definitions only; prove it under Proof/")
    return out


def native_tcb(
    tcb: dict[str, str | None],
    libraries: dict[str, frozenset[str]],
    lib_names: dict[str, str],
    traces: dict[str, frozenset[str]],
    targets: set[str],
) -> list[str]:
    """Problems with TCB/'s precompiled libraries: `tcb` maps each module of
    TCB/ to its target (None for one in no target's directory), `libraries`
    each precompiled library to its modules and `lib_names` to its `libName`,
    and `traces` each module to what its build reads (ordinary and native)."""
    out = []
    for m in sorted(tcb):
        libs = sorted(n for n, members in libraries.items() if m in members)
        if len(libs) != 1:
            out.append(f"{m}: in {len(libs)} precompiled libraries ({', '.join(libs) or 'none'}); "
                       f"list it in exactly one, {native_tcb_name(tcb[m], m)}, in lean/lakefile.toml")
            continue
        if libs[0] != native_tcb_name(tcb[m], m):
            out.append(f"{m}: in {libs[0]}; it belongs in {native_tcb_name(tcb[m], m)} (lean/lakefile.toml)")
    for t in sorted(targets):
        lib = native_tcb_name(t)
        if lib in libraries and lib_names.get(lib) != f"VerifiedGarbage_{lib}":
            out.append(f"{lib}: give it `libName = \"VerifiedGarbage_{lib}\"` (lean/lakefile.toml), "
                       "the shared library the emitter loads")
    native = {m: n for n, members in libraries.items() for m in members}
    for t in sorted(targets):
        changed = {m for m, mt in tcb.items() if mt == t}
        own = native_tcb_name(t)
        for m in sorted(lean_shards.stale_of(changed, traces) - changed):
            other = target_of(m.split("."), targets)
            if other and other != t:
                out.append(f"{m}: of {other}, rebuilt by a change to {t}'s TCB/")
            elif native.get(m, own) not in (own, None) and other != t:
                out.append(f"{m}: a module of {native[m]}, rebuilt by a change to {t}'s TCB/ "
                           "(imports from TCB/ only what no target owns)")
    return out


# The modules of the audit records, and their library (lean/lakefile.toml), a
# plugin of every other one.
AUDIT_RECORDS = frozenset({"VerifiedGarbage.TCB.AuditBase", "VerifiedGarbage.TCB.AuditRecords"})


def native_tcb_name(target: str | None, module: str | None = None) -> str:
    """The precompiled library of TCB/'s modules of `target` (of `module`, if
    given: the audit records' modules have their own)."""
    if module in AUDIT_RECORDS:
        return "NativeAuditRecords"
    return f"NativeTCB{target or ''}"


def full_closures(imps: dict[str, list[str]], starts: list[str]) -> dict[str, frozenset[str]]:
    """`lean_shards.closures` of `starts` and of what they import alone."""
    reach, stack = set(), list(starts)
    while stack:
        if (m := stack.pop()) not in reach:
            reach.add(m)
            stack += imps[m]
    return lean_shards.closures({m: imps[m] for m in reach})


def check_native_tcb(targets: set[str], mods: dict[str, pathlib.Path],
                     texts: dict[pathlib.Path, str]) -> list[str]:
    """`native_tcb` on the project (`lean_shards.modules()`, and each one's
    text), with ci/lean_shards.py's traces of the targets' modules of TCB/
    alone (`among`), and native traces only for the modules of precompiled
    libraries, which alone have them."""
    imps, vis, modes = {}, {}, {}
    for m, f in mods.items():
        imps[m], vis[m], modes[m] = lean_shards.parse_imports(texts[f], mods)
    tcb = {m: target_of(m.split("."), targets) for m in mods if m.startswith("VerifiedGarbage.TCB.")}
    among = frozenset(m for m, t in tcb.items() if t)
    traces = lean_shards.reads(imps, lean_shards.closures(imps, among), vis, modes, among)
    config = tomllib.loads((lean_shards.LEAN / "lakefile.toml").read_text())
    # A library's modules, from the whole closures of its `roots` alone.
    roots = [r for lib in config.get("lean_lib", []) for r in lib.get("roots", []) if r in imps]
    libraries = lean_shards.precompiled_libraries(dict.fromkeys(imps, frozenset()) | full_closures(imps, roots))
    full = full_closures(imps, [m for members in libraries.values() for m in members])
    native = lean_shards.native_reads(imps, full, libraries, lean_shards.native_trace_modules(full))
    for m, r in native.items():
        traces[m] = traces[m] | (r & among)
    lib_names = {lib["name"]: lib.get("libName", "") for lib in config.get("lean_lib", [])}
    return native_tcb(tcb, libraries, lib_names, traces, targets)


def imports(text: str):
    """Each import of a file's `text`, with its line number."""
    # Most lines are not imports: find those with the word, and match each
    # once, from its start.
    line, counted = 1, 0
    pos = text.find("import")
    while pos >= 0:
        start = text.rfind("\n", 0, pos) + 1
        line += text.count("\n", counted, start)
        counted = start
        if m := IMPORT_ANY.match(text, start):
            yield line, m.group(1)
        end = text.find("\n", pos)
        if end < 0:
            break
        pos = text.find("import", end + 1)


def main() -> int:
    # Every check reads each file of the project once, from here.
    mods = lean_shards.modules()
    texts = {f: f.read_text() for f in mods.values()}
    errors = tcb_lemmas(LEAN, texts)
    targets = {p.name for p in (LEAN / "TCB").iterdir() if p.is_dir()}
    lean = len(str(LEAN)) + 1
    for f in sorted(LEAN.rglob("*.lean")):
        own = target_of(str(f)[lean : -len(".lean")].split("/"), targets)
        if own is None:
            continue
        for n, mod in imports(texts[f]):
            other = mod.startswith("VerifiedGarbage.") and target_of(mod.split("."), targets)
            if other and other != own:
                errors.append(f"{f.relative_to(ROOT)}:{n}: a module of {own} may not import {mod}, of {other}")
    errors += check_native_tcb(targets, mods, texts)
    for d, prefixes in ALLOWED_IMPORTS.items():
        for f in sorted((LEAN / d).rglob("*.lean")):
            for n, mod in imports(texts[f]):
                if not allowed(mod, prefixes):
                    errors.append(f"{f.relative_to(ROOT)}:{n}: {d}/ may not import {mod}")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("Lean imports OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
