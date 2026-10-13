#!/usr/bin/env python3
"""Converts Lean files to modules of Lean's module system, keeping what
every importer sees. It was used to convert the library, a layer at a time;
it is kept for the one-off pass that makes imports private, and goes after
it. New files are written as modules by hand (CLAUDE.md, "Lean modules"),
and `ci/check_lean_modules.py` checks that they are.

  modularize.py PATH...   convert each `.lean` file at PATH (a file or a
                          directory, recursively) that is not a module yet
  modularize.py visibility [--additions-only] PATH...
                          after `lake build`: in the modules under PATH,
                          make plain each `public import` their public
                          surface does not need, and add the direct
                          imports a module needs once its imports'
                          imports are no longer public (only those, with
                          `--additions-only`); `D/*` is D's own files:
                          see "Import visibility"

A converted file starts with `module`; its imports become `public import`;
and its body is an `@[expose] public section`, so that every declaration
stays visible to importers with its definition, as before.

A file that only defines tactics, elaborators or commands (it declares
`elab`, `syntax`, `macro` or `simproc`s, and no theorem, nor a command that
adds one, nor a structure, inductive type or instance unless it imports
`Lean`) is meta code: its
body is a `public meta section`, so that its definitions run at elaboration
time in the files that use them, and each of its imports is also a
`public meta import` (only that, for `Lean`'s), so that its code can run
theirs. A file that declares such meta code next to definitions or theorems
(marking `meta` the definitions its tactics run) imports `Lean` both ways:
`public import` and `public meta import`.

A file that evaluates code while it is elaborated (`#guard`, `#eval`,
`run_cmd`, ..., and the framework's `materialize_*` and `taint_decide`/
`taint_summary`, which run code to build literals and hints) also imports each of its imports as `meta import`, so that
what it evaluates is available to the compiler at that time.

A proof module (under `Proof/`, but not the framework) also imports the core
modules of `CORE_ALL` with `import all`, and those of `CORE_ALL_FOR` whose
definition it mentions.

A leading comment (a copyright notice) stays before `module`.

Import visibility (`visibility`). A module's plain (private) `import X`
gives it X for its proofs, but not to the modules that import it: they see
only its public imports, transitively. A file that is not a module (the
emitter's drivers, `Artifacts.lean`, the known-answer tests) still loads and
sees everything, private imports included, so the audits still see every
proof (`ci/audit_negative.py` checks it). After `lake build`,
`lean/ImportUses.lean` lists for each module the modules whose constants its
public surface mentions (the types of its declarations, the values of its
definitions, which are exposed) and those it uses anywhere. From that, a
`public import X` stays public when X's public closure (X and what it
imports publicly, transitively, after the change) has a module the public
surface mentions; when X is outside this project; or when the module, or X,
declares syntax, attributes or `simp` lemmas (which change how importers
elaborate without leaving a constant behind). Then every module whose
imports no longer give it what it uses (a constant, in a proof too), or a
module outside this project or of that kind which it sees today, gets a
direct import of it: `public import` if its public surface needs it, plain
`import` otherwise, and `meta import` too in a file that evaluates code. The
added imports change nothing before the demotions, so they can merge first.
Like the emitter, it loads every module at once: on Linux it needs
`vm.max_map_count` raised (lean/README.md).
"""

import pathlib
import re
import subprocess
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

IMPORT = re.compile(r"^import\s+(\S+)\s*$")
META_DECL = re.compile(r"^(elab|syntax|macro|macro_rules|simproc|dsimproc|elab_rules)\b", re.M)
THEOREM = re.compile(r"^(@\[[^\]]*\]\s*)?(private\s+)?(theorem|lemma)\b", re.M)
META_MARK = re.compile(r"^\s*(@\[[^\]]*\]\s*)?((public|private|protected)\s+)?meta\s+(def|instance|section|abbrev|structure)\b", re.M)
EVAL_CMD = re.compile(r"^\s*(#guard|#eval|#reduce|run_cmd|run_elab|run_meta|materialize_\w+)\b", re.M)
EVAL_NAMES = ["taint_decide", "taint_summar"]


def evaluates(text: str, names: list[str]) -> bool:
    """Whether `text` runs code while it is elaborated: an evaluating command,
    a tactic or command whose name contains one of `EVAL_NAMES`, or one of the
    other `names` (not in a docstring's backquotes, a string, or a syntax
    quotation)."""
    if EVAL_CMD.search(text):
        return True
    pre = r"(^|[\s;·>]|(?<!`)\()"
    base = "|".join(re.escape(n) for n in EVAL_NAMES)
    if re.search(pre + r"\w*(" + base + r")\w*\b", text, re.M):
        return True
    others = [n for n in names if n not in EVAL_NAMES]
    return bool(others) and re.search(pre + r"(" + "|".join(map(re.escape, others)) + r")\b(?!`)",
                                      text, re.M) is not None


# A tactic or command defined by `macro "name" … => body` or `elab "name" …`,
# or by `macro_rules`/`elab_rules` on `(tactic| name …)`: its name and body.
DEFINES = re.compile(r'^(?:macro|elab)\b[^"\n]*"(\w+)|^(?:macro_rules|elab_rules)\b', re.M)
QUOTED = re.compile(r"`\((?:tactic|command)\|\s*(\w+)")


def blocks(text: str):
    """The top-level `macro`/`elab`/`…_rules` blocks of `text`: (names, body)."""
    starts = [m for m in DEFINES.finditer(text)]
    for k, m in enumerate(starts):
        end = text.find("\n\n", m.end())
        body = text[m.start():end if end >= 0 else len(text)]
        names = [m.group(1)] if m.group(1) else [q for q in QUOTED.findall(body.split("=>")[0])]
        yield names, body.split("=>", 1)[1] if "=>" in body else body


def evaluating_names(lean: pathlib.Path) -> list[str]:
    """`EVAL_NAMES`, and the project's tactics and commands whose definition
    runs one of them or evaluates a term itself (`evalExpr`), to a fixpoint:
    e.g. `kem_wf`, a macro for `taint_decide`, and `def_literal`."""
    bs = [b for f in (lean / "VerifiedGarbage" / "Proof").rglob("*.lean") for b in blocks(f.read_text())]
    names = list(EVAL_NAMES)
    while True:
        new = {n for ns, body in bs if evaluates(body, names) or "evalExpr" in body for n in ns if n not in names}
        if not new:
            return names
        names += sorted(new)


def is_module(lines: list[str]) -> bool:
    comment = False
    for l in lines:
        s = l.strip()
        if comment:
            comment = not s.endswith("-/")
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
            continue
        if s == "module":
            return True
        if s and not s.startswith("--"):
            return False
    return False


# Lean core modules with definitions the proofs evaluate (with `decide`,
# `rfl` or the kernel, e.g. Spec tables built with `Array.ofFn`) but that core
# does not expose to modules. A proof module imports them with `import all`,
# so that it sees their bodies as a non-module file does.
CORE_ALL = ["Init.Data.Array.Basic", "Init.Data.Array.DecidableEq", "Init.Data.Nat.Bitwise.Basic",
            "Init.Data.Vector.Basic"]
# Core modules a proof module imports with `import all` only if it mentions
# their definition: `Nat.isPowerOfTwo`, which core states as `∃ k, n = 2 ^ k`
# but neither exposes nor gives a lemma to take apart.
CORE_ALL_FOR = {"Init.Data.Nat.Power2.Basic": "isPowerOfTwo"}

# Commands that add theorems (and definitions) to the file that runs them.
PROOF_CMD = re.compile(r"^(materialize_\w+|taint_summary)\b", re.M)


# Declarations of data (not `meta`): a file with one is meta code only if
# it imports `Lean` (a tactic's own state, as in `Framework/SigEval.lean`).
DATA = re.compile(r"^(@\[[^\]]*\]\s*)?((private|protected)\s+)?(structure|inductive|class|instance)\b", re.M)


def is_meta(text: str, imports: list[str]) -> bool:
    uses_lean = any(i == "Lean" or i.startswith("Lean.") for i in imports)
    return (META_DECL.search(text) is not None and THEOREM.search(text) is None
            and PROOF_CMD.search(text) is None and (uses_lean or DATA.search(text) is None))


def is_proof(path: str) -> bool:
    p = pathlib.PurePosixPath(path).as_posix()
    return "VerifiedGarbage/Proof/" in p and "VerifiedGarbage/Proof/Framework/" not in p


def convert(text: str, proof: bool = False, names: list[str] = EVAL_NAMES) -> str:
    lines = text.split("\n")
    if is_module(lines):
        return text
    i, n, lead = 0, len(lines), []
    # A leading comment (a copyright notice) stays before `module`.
    if lines and lines[0].startswith("/-") and not lines[0].startswith("/-!"):
        while i < n:
            lead.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
    head = []
    while i < n and (IMPORT.match(lines[i]) or lines[i].strip() == "" or lines[i].startswith("--")):
        head.append(lines[i])
        i += 1
    imports = [IMPORT.match(l).group(1) for l in head if IMPORT.match(l)]
    meta = is_meta(text, imports)
    evals = not meta and evaluates(text, names)
    # Tactics next to definitions and theorems: their code needs Lean at
    # elaboration time too.
    mixed = not meta and (META_DECL.search(text) is not None or META_MARK.search(text) is not None)
    out = lead + ["module", ""]
    for l in head:
        m = IMPORT.match(l)
        if m:
            core = m.group(1) == "Lean" or m.group(1).startswith("Lean.")
            l = f"public {'meta ' if meta and core else ''}import {m.group(1)}"
            if meta and not core:
                l += f"\npublic meta import {m.group(1)}"
            if mixed and core:
                l += f"\npublic meta import {m.group(1)}"
            if evals:
                l += f"\nmeta import {m.group(1)}"
        out.append(l)
    while out and out[-1].strip() == "":
        out.pop()
    if proof and not meta:
        out += [f"import all {m}" for m in CORE_ALL]
        out += [f"import all {m}" for m, name in CORE_ALL_FOR.items() if name in text]
    out.append("")
    # The module's docstring stays right after the imports.
    if i < n and lines[i].startswith("/-!"):
        while i < n:
            out.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
        out.append("")
    out.append("public meta section" if meta else "@[expose] public section")
    out.append("")
    while i < n and lines[i].strip() == "":
        i += 1
    out += lines[i:]
    return "\n".join(out)


# Import visibility (`visibility`): which `public import`s can be plain
# (private) `import`s.

# Declarations that change how importers parse or elaborate, without leaving a
# constant in what they elaborate: a module declaring one is imported
# publicly, and every module keeps seeing it.
SURFACE_SYNTAX = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:scoped|local)\s+)?"
    r"(syntax|macro|macro_rules|elab|elab_rules|notation|infixl?|infixr|prefix|postfix|"
    r"simproc|dsimproc|declare_syntax_cat|attribute\s+\[)\b", re.M)
SIMP_ATTR = re.compile(r"@\[[^\]]*\bsimp\b")
VIS_IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)\s*$")


def module_path(name: str) -> pathlib.Path:
    return LEAN / (name.replace(".", "/") + ".lean")


def read_uses(path: pathlib.Path) -> dict:
    """The lines `ImportUses.lean` writes, by module: (imports as (name,
    public, meta), modules of the public surface, modules used anywhere,
    whether it declares meta code, the namespaces under `VG` its constants
    are in)."""
    mods = {}
    for line in path.read_text().splitlines():
        name, imps, pub, used, meta, nss = line.split("\t")
        imports = []
        for i in filter(None, imps.split(",")):
            base = i.split("+")[0]
            imports.append((base, "+p" in i, "+m" in i))
        mods[name] = (imports, set(filter(None, pub.split(","))),
                      set(filter(None, used.split(","))), meta == "meta",
                      set(filter(None, nss.split(","))))
    return mods


OPEN = re.compile(r"^\s*open\s+(?:scoped\s+)?([^(\n]*)", re.M)
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)", re.M)


def opened_namespaces(text: str) -> list[list[str]]:
    """For each namespace an `open` in `text` names: the names it may resolve
    to (relative to each enclosing `namespace` in the file, or absolute)."""
    prefixes = {""}
    for m in NAMESPACE.finditer(text):
        parts = m.group(1).split(".")
        prefixes |= {".".join(parts[:i]) + "." for i in range(1, len(parts) + 1)}
    out = []
    for m in OPEN.finditer(text):
        for word in m.group(1).split():
            if word in ("in", "hiding", "renaming") or not re.match(r"^[A-Za-z_][\w.']*$", word):
                break
            out.append(sorted({p + word for p in prefixes}))
    return out


def plan_visibility(mods: dict) -> dict:
    """For each module of this project whose imports change: (the imports
    that become plain `import`s, the `public import`s to add, the `import`s to
    add), keeping every module's sight of what it uses.

    A `public import X` stays public when X's public closure (X and what it
    imports publicly, transitively, after this plan) has a module whose
    constants the module's public surface mentions, or when X is outside this
    project or declares syntax, attributes or `simp` lemmas, which change how
    importers elaborate without leaving a constant behind. Then each module
    gets a direct import of what it no longer sees but uses (a constant, in
    a proof too) or sees today and is outside this project or such a module:
    `public import` for what its public surface needs, plain `import`
    otherwise (with `meta import` too in a file that evaluates code)."""
    names = list(mods)
    idx = {n: i for i, n in enumerate(names)}
    project = {n for n in names if n.startswith("VerifiedGarbage.")}
    src = {}
    for n in project:
        p = module_path(n)
        src[n] = p.read_text() if p.exists() else ""
    surface = {n for n in project
               if mods[n][3] or SURFACE_SYNTAX.search(src[n]) or SIMP_ATTR.search(src[n])}
    keep = {n for n in names if n not in project or n in surface or not is_module(src[n].split("\n"))}
    implicit = {n for n in names if n == "Init" or n.startswith("Init.")}
    bit = lambda ns: sum(1 << idx[n] for n in ns if n in idx)
    ns_owners: dict[str, set] = {}
    for n in project:
        for ns in mods[n][4]:
            ns_owners.setdefault(ns, set()).add(n)

    def order():
        seen, out = set(), []
        for root in names:
            stack = [(root, iter(mods[root][0]))]
            if root in seen:
                continue
            seen.add(root)
            while stack:
                n, it = stack[-1]
                nxt = next((m for m, _, _ in it if m in mods and m not in seen), None)
                if nxt is None:
                    out.append(n)
                    stack.pop()
                else:
                    seen.add(nxt)
                    stack.append((nxt, iter(mods[nxt][0])))
        return out

    # What a module sees: its imports (`meta` ones too, for its meta code),
    # and what they import publicly, transitively.
    def closures(public_of):
        clo = {}
        for n in order():
            c = 1 << idx[n]
            for m in public_of(n):
                c |= clo[m]
            clo[n] = c
        return clo

    old_pub = lambda n: [m for m, p, mt in mods[n][0] if p and m in mods]
    old_clo = closures(old_pub)
    keep_bits = bit(keep - implicit)
    plan, new_pub_edges = {}, {}
    new_clo = {}
    for n in order():
        imports = mods[n][0]
        if n not in project or not is_module(src[n].split("\n")):
            new_pub_edges[n] = old_pub(n)
        else:
            pub_need = bit(mods[n][1] - implicit) & ~(1 << idx[n])
            public, private, optional = [], [], []
            for m, p, mt in imports:
                if m not in mods:
                    continue
                if p and (mt or n in keep or m in keep):
                    public.append(m)
                elif p and new_clo[m] & pub_need:
                    optional.append(m)
                else:
                    private.append((m, p))
            # Keep public only enough of the others to cover what the public
            # surface needs: each time, the import that covers the most of
            # what is left for the least it adds to what importers see.
            sees_pub = 0
            for m in public:
                sees_pub |= new_clo[m]
            while pub_need & ~sees_pub and optional:
                def cost(m):
                    gain = (new_clo[m] & pub_need & ~sees_pub).bit_count()
                    return (-(gain / (1 + (new_clo[m] & ~sees_pub).bit_count())), m) if gain else (1, m)
                best = min(optional, key=cost)
                if cost(best)[0] == 1:
                    break
                optional.remove(best)
                public.append(best)
                sees_pub |= new_clo[best]
            private += [(m, True) for m in optional]
            demoted = [m for m, p in private if p]
            add_pub = cover(pub_need & ~sees_pub, names, new_clo)
            for m in add_pub:
                sees_pub |= new_clo[m]
            sees = sees_pub
            for m, _ in private:
                sees |= new_clo[m]
            old_sees = 0
            for m, _, mt in imports:
                if m in mods:
                    old_sees |= old_clo[m]
            need = bit(mods[n][2] - implicit) | (old_sees & keep_bits)
            # What a module uses it sees today: an import added for it changes
            # what no module sees, and adds no dependency.
            unseen = need & ~old_sees & ~(1 << idx[n])
            if unseen:
                bad = [names[i] for i in range(unseen.bit_length()) if unseen >> i & 1]
                raise SystemExit(f"{n} uses {bad[:3]}, which it does not see: rerun ImportUses.lean")
            add = cover(need & ~sees & ~(1 << idx[n]), names, new_clo)
            for m in add:
                sees |= new_clo[m]
            # An `open` needs a module declaring the namespace: keep one in
            # sight, one the module sees today (an import, as above, that
            # changes what no module sees).
            for cands in opened_namespaces(src[n]):
                owners = bit(o for ns in cands for o in ns_owners.get(ns, ()))
                if owners & old_sees and not owners & (sees | 1 << idx[n]):
                    m = min((names[i] for i in range(owners.bit_length()) if owners >> i & 1 and old_sees >> i & 1),
                            key=lambda o: (-new_clo[o].bit_count(), o), default=None)
                    if m is not None:
                        add.append(m)
                        sees |= new_clo[m]
            if demoted or add_pub or add:
                plan[n] = (demoted, add_pub, add)
            new_pub_edges[n] = public + add_pub
        c = 1 << idx[n]
        for m in new_pub_edges[n]:
            c |= new_clo[m]
        new_clo[n] = c
    return plan


def cover(missing: int, names: list[str], clo: dict) -> list[str]:
    """Modules whose public closures together cover the bit set `missing`,
    taking the largest closures first (a closure contains those of the
    modules in it)."""
    ms = [names[i] for i in range(missing.bit_length()) if missing >> i & 1]
    ms.sort(key=lambda m: (-clo[m].bit_count(), m))
    out, covered = [], 0
    for m in ms:
        if not (missing & ~covered):
            break
        if (missing & ~covered) & clo[m] and not covered >> names_idx(names)[m] & 1:
            out.append(m)
            covered |= clo[m]
    assert missing & ~covered == 0
    return sorted(out)


_IDX = {}


def names_idx(names: list[str]) -> dict:
    if id(names) not in _IDX:
        _IDX[id(names)] = {n: i for i, n in enumerate(names)}
    return _IDX[id(names)]


def apply_visibility(text: str, demoted: list[str], add_pub: list[str], add: list[str]) -> str:
    """`text` with each `public import` of `demoted` a plain `import` (dropped
    if the file also has `import all` of it) and the imports `add_pub`
    (public) and `add` added after its last import."""
    lines = text.split("\n")
    has_all = {m.group(4) for l in lines if (m := VIS_IMPORT.match(l)) and m.group(3)}
    evaluates_code = any((m := VIS_IMPORT.match(l)) and m.group(2) and not m.group(1) for l in lines)
    out, last = [], -1
    for l in lines:
        m = VIS_IMPORT.match(l)
        if m and m.group(1) and not m.group(2) and not m.group(3) and m.group(4) in demoted:
            if m.group(4) not in has_all:
                out.append(f"import {m.group(4)}")
        else:
            out.append(l)
        if VIS_IMPORT.match(out[-1] if out else ""):
            last = len(out) - 1
    new = [f"public import {m}" for m in add_pub] + [f"import {m}" for m in add]
    if evaluates_code:
        new += [f"meta import {m}" for m in add_pub + add]
    return "\n".join(out[:last + 1] + new + out[last + 1:])


def module_names(lean: pathlib.Path) -> list[str]:
    """The modules of the library (files under `VerifiedGarbage/` that are)."""
    return sorted(".".join(f.relative_to(lean).with_suffix("").parts)
                  for f in (lean / "VerifiedGarbage").rglob("*.lean")
                  if is_module(f.read_text().split("\n")))


def visibility(paths: list[str], additions_only: bool) -> int:
    """Applies `plan_visibility` to the files under `paths`, from what
    `ImportUses.lean` finds in the built library."""
    out = LEAN / ".lake" / "import-uses.tsv"
    r = subprocess.run(["lake", "env", "lean", "--run", "ImportUses.lean", str(out)] + module_names(LEAN),
                       cwd=LEAN)
    if r.returncode:
        return r.returncode
    plan = plan_visibility(read_uses(out))
    # `D/*` is D's own files, `D` every file under D.
    own = [pathlib.Path(p[:-2]).resolve() for p in paths if p.endswith("/*")]
    roots = [pathlib.Path(p).resolve() for p in paths if not p.endswith("/*")]
    changed = 0
    for n, (demoted, add_pub, add) in sorted(plan.items()):
        f = module_path(n).resolve()
        if not (f.parent in own or any(f.is_relative_to(r) for r in roots)):
            continue
        text = f.read_text()
        new = apply_visibility(text, [] if additions_only else demoted, add_pub, add)
        if new != text:
            f.write_text(new)
            changed += 1
    print(f"{changed} files changed", file=sys.stderr)
    return 0



def main(args: list[str]) -> int:
    if args and args[0] == "visibility":
        rest = [a for a in args[1:] if a != "--additions-only"]
        return visibility(rest, "--additions-only" in args) if rest else 2
    if not args:
        print(__doc__, file=sys.stderr)
        return 2
    files = []
    for a in args:
        p = pathlib.Path(a)
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    names = evaluating_names(LEAN)
    changed = 0
    for f in files:
        text = f.read_text()
        new = convert(text, is_proof(str(f)), names)
        if new != text:
            f.write_text(new)
            changed += 1
    print(f"{changed} of {len(files)} files converted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
