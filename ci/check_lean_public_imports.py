#!/usr/bin/env python3
"""Checks that the modules a change edits import privately what they use only
privately, and import nothing they do not use (CLAUDE.md, "Lean modules").
Run it before pushing, after building the modules, which `lake shake` reads;
it exits non-zero naming each import to change, and `--fix` changes them.
Not run in CI: `lake shake` alone takes most of a minute.

A module's `public import X` makes every module importing it read `X`'s
outputs too (`lean_shards.reads`): a change to `X`'s statements then rebuilds
all of them. Imported privately, `X` rebuilds only the module itself, whose
outputs come out as they were, and Lake stops there. So a `public import` of a
module of the project that the module's own statements and exposed
definitions do not use (as `lake shake` finds from the module's `.olean`) must
be a plain `import`; the modules that use `X` import it themselves.

`lake shake` sees the declarations, instances, syntax and attributes a module
uses, not the effects of a module that only changes how others elaborate
(an `attribute [...]`, a `macro_rules`, a `seal`, a `materialize_*` literal
that `lit_decide` reads: `side_effects`). The check never asks to stop
re-exporting such a module: where making `X` private would hide one (or a
module of a dependency) from the importers, it names the `public import`s
that keep passing it on. An import that must stay public for another reason
says so after it: `public import X -- shake: keep`, which `lake shake` then
leaves alone.

  check_lean_public_imports.py PLAN       the modules of `edited` in the plan
                                          (`lean_shards.py plan`)
  check_lean_public_imports.py -m M...    the modules M
  … --dependencies PREFIX...              also the imports of these
                                          dependencies' modules (e.g. Mathlib)
                                          that shake finds unused
                                          (`narrow_dependencies`)
  … --base REV                            only the public imports they added
                                          since REV (CI: the pull request's
                                          base), so that an edit is not held to
                                          imports it did not touch
"""

import argparse
from dataclasses import asdict, dataclass, field
import json
import pathlib
import re
import shutil
import subprocess
import sys
import time

import lean_source_evidence
import check_lean_imports as import_discipline
import lean_import_build
import lean_cache
from lean_import_graph import VisibilityGraph

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
# The library the check covers.
LIBRARY = "VerifiedGarbage"
DECLARATION_VIEWS = ("public", "private", "meta_public", "meta_private")
# More edited modules than this (a missing manifest, which makes every module
# edited) would take `lake shake` minutes: the check then covers none.
MAX_MODULES = 3000
IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)")
# Commands whose effect on the modules importing a module no declaration of
# it records: global attributes, syntax, sealing, unification hints,
# instance priorities, and the literals of `materialize_*` and summaries of
# `taint_summary`, which tactics read without naming them.
SIDE_EFFECTS = re.compile(
    r"^\s*(attribute \[|seal |unseal |register_simp_attr|macro_rules|macro |elab |syntax |notation|infix|"
    r"prefix|postfix|declare_syntax_cat|elab_rules|@\[(term_)?elab|@\[macro|@\[tactic|@\[simproc|@\[dsimproc|"
    r"(builtin_)?d?simproc |unif_hint|instance \(priority|scoped|@\[default_instance|materialize_|taint_summary|"
    r"local_notation)",
    re.M,
)
# Instances can be selected by temporary evaluation that leaves no constant
# reference in either saved declarations or the source index.
INSTANCE_DECLS = re.compile(r"\b(?:instance|deriving)\b")
INITIALIZER_DECLS = re.compile(
    r"^\s*(?:(?:public|private|protected|meta|unsafe)\s+)*(?:builtin_initialize|initialize)\b", re.M)
INSTANCE_EXTENSION = "Lean.Meta.instanceExtension"
# These entries describe declarations, their generated code and source/name
# bookkeeping. Search registries and unfamiliar extensions are deliberately
# absent: e.g. Aesop names extensions after arbitrary user-defined rule sets.
# Exact private names make a changed Lean representation conservative too.
STRUCTURAL_EXTENSIONS = frozenset({
    "Lean.deprecatedModuleExt", "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt",
    "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
    "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt",
    "_private.Lean.Namespace.0.Lean.namespacesExt",  # checked separately for opens
    "Lean.IR.declMapExt", "Lean.Compiler.LCNF.baseExt", "Lean.Compiler.LCNF.impureSigExt",
    "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.monoTypeExt", "Lean.Compiler.LCNF.specExtension",
    "Lean.Compiler.inlineAttrs", "reducibilityCore", "Lean.backwardDefeqAttr", "Lean.defeqAttr",
    "Lean.auxRecExt", "Lean.protectedExt", "Lean.projectionFnInfoExt", "Lean.noConfusionExt",
    "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt",
    "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt",
    "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt",
    "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt",
    "_private.Lean.Structure.0.Lean.structureExt", "Lean.Meta.Match.Extension.extension", "recExt",
    "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt", "Lean.Elab.Structural.eqnInfoExt",
    "_private.Lean.Meta.Constructions.SparseCasesOn.0.Lean.Meta.sparseCasesOnInfoExt",
    "_private.Lean.Compiler.MetaAttr.0.Lean.metaExt", "Lean.Meta.congrKindsExt",
    "Lean.Meta.completionBlackListExt", "Lean.noncomputableExt",
})


def header_lines(lines):
    """Header commands and their line numbers, skipping nested Lean comments.

    Stop at module documentation, as the project's headers precede it.
    This is shared by graph construction and editing so they see the same edges.
    """
    depth = 0
    for n, line in enumerate(lines):
        code, i = "", 0
        while i < len(line):
            if not depth and line.startswith("/-!", i):
                return
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth and line.startswith("-/", i):
                depth -= 1
                i += 2
                code += " "
            elif depth:
                i += 1
            elif line.startswith("--", i):
                break
            else:
                code += line[i]
                i += 1
        s = code.strip()
        if not s:
            continue
        if s in ("module", "prelude") or IMPORT.fullmatch(s):
            yield n, s
        else:
            return


def header(text: str) -> list[tuple[str, bool, bool, bool]]:
    """The imports of a source's header: (module, public, meta, all)."""
    out = []
    for _, s in header_lines(text.splitlines()):
        m = IMPORT.fullmatch(s)
        if m:
            out.append((m.group(4), bool(m.group(1)), bool(m.group(2)), bool(m.group(3))))
    return out


def is_module(text: str) -> bool:
    return next((s == "module" for _, s in header_lines(text.splitlines())), False)


@dataclass(frozen=True, order=True)
class Edit:
    module: str
    action: str  # demote, remove, remove_public, remove_meta, add, add_public, add_meta, add_public_meta
    dependency: str


NARROWING = frozenset({"demote", "remove", "remove_public", "remove_meta"})


@dataclass
class Plan:
    """Executable operations, separate from human diagnostics. Not build verified."""
    edits: list[Edit] = field(default_factory=list)
    messages: list[str] = field(default_factory=list)
    blocked: list[str] = field(default_factory=list)
    deferred: list[dict] = field(default_factory=list)
    decisions: list[dict] = field(default_factory=list)

    def paths(self) -> set[pathlib.Path]:
        return {graph_path(e.module) for e in self.edits}

    def exclude_reviewed(self) -> None:
        # A repair and the demotion requiring it must stay together. Until
        # plans have independent groups, block the entire batch conservatively.
        protected = sorted({e.module for e in self.edits if reviewed(e.module)})
        if protected:
            self.blocked.append("manual edits required in: " + ", ".join(protected))


def reviewed(mod: str) -> bool:
    return any(part in REVIEWED for part in mod.split("."))


def module_annotations(text: str) -> set[str]:
    lines = text.splitlines()
    for n, s in header_lines(lines):
        if s == "module":
            return set(re.findall(r"shake:\s*(keep-all|keep-downstream)\b", lines[n]))
    return set()


class Graph(VisibilityGraph):
    """The imports of the project's modules and its dependencies' (read
    lazily, from the sources Lake builds them from)."""

    def __init__(self, roots: list[pathlib.Path], dependencies: tuple[str, ...] = ()):
        super().__init__()
        self.roots = roots
        # The dependencies (by module prefix, e.g. `Mathlib`) whose imports
        # the check may propose to remove (`narrow_dependencies`).
        self.dependencies = tuple(dependencies)
        self.files: dict[str, pathlib.Path | None] = {}
        self.texts: dict[str, str] = {}
        self.users: dict[str, set[str]] | None = None
        self.keep_cache: dict[str, bool] = {}
        self.project_cache: dict[str, bool] = {}
        self.implicit_cache: dict[str, bool] = {}
        self.import_cache: dict[str, list[tuple[str, bool, bool, bool]]] = {}
        self.effect_checked: set[str] = set()
        self.opaque_extensions: dict[str, list[str]] = {}
        self.namespace_exports: dict[str, set[str]] = {}
        self.load_order_cache: dict[tuple[str, bool], tuple[str, ...]] = {}

    def load_order(self, mod: str, ordinary_only: bool = False) -> tuple[str, ...]:
        """Dependency-first import order, including private and meta paths."""
        key = (mod, ordinary_only)
        if key not in self.load_order_cache:
            stack, active, finished, ordered = [(mod, False)], set(), set(), []
            while stack:
                current, ready = stack.pop()
                if current in finished:
                    continue
                if ready:
                    active.remove(current)
                    finished.add(current)
                    ordered.append(current)
                else:
                    if current in active:
                        raise ValueError(f"cyclic import graph at {current}")
                    active.add(current)
                    stack.append((current, True))
                    stack.extend((dep, False) for dep, _, meta, _ in reversed(self.imports(current))
                                 if dep not in finished and not (ordinary_only and meta))
            self.load_order_cache[key] = tuple(ordered)
        return self.load_order_cache[key]

    def importers(self, mod: str, library: list[str]) -> set[str]:
        if self.users is None:
            self.users = reverse_index(library)
        return reverse_closure(mod, self.users)

    def path(self, mod: str) -> pathlib.Path | None:
        if mod not in self.files:
            rel = pathlib.Path(*mod.split(".")).with_suffix(".lean")
            self.files[mod] = next((r / rel for r in self.roots if (r / rel).is_file()), None)
        return self.files[mod]

    def text(self, mod: str) -> str:
        if mod not in self.texts:
            p = self.path(mod)
            self.texts[mod] = p.read_text(errors="replace") if p else ""
        return self.texts[mod]

    def imports(self, mod: str) -> list[tuple[str, bool, bool, bool]]:
        if mod not in self.import_cache:
            text = self.text(mod)
            module = is_module(text)
            explicit = [(i, p or not module, me, a) for i, p, me, a in header(text)]
            # HeaderSyntax.imports implicitly supplies BOTH phases of Init,
            # exported even in a `module`, unless `prelude` is present. These
            # edges are absent from .ilean's directImports and from the source.
            implicit = [] if not self.has_implicit_init(mod) else [
                ("Init", True, False, False), ("Init", True, True, False)]
            self.import_cache[mod] = implicit + explicit
        return self.import_cache[mod]

    def project(self, mod: str) -> bool:
        if mod not in self.project_cache:
            p = self.path(mod)
            self.project_cache[mod] = p is not None and p.is_relative_to(LEAN / LIBRARY)
        return self.project_cache[mod]

    def dependency(self, mod: str) -> bool:
        """Whether `mod` is a module of a dependency named by `dependencies`."""
        return (not self.project(mod)
                and any(mod == d or mod.startswith(d + ".") for d in self.dependencies))

    def has_implicit_init(self, mod: str) -> bool:
        if mod not in self.implicit_cache:
            text = self.text(mod)
            self.implicit_cache[mod] = bool(text) and not any(s == "prelude" for _, s in header_lines(text.splitlines()))
        return self.implicit_cache[mod]

    def implicit_reads(self, mod: str, meta: bool = False) -> frozenset[str]:
        """Capabilities supplied automatically, which need no explicit repair."""
        if not self.has_implicit_init(mod):
            return frozenset()
        return self.meta_passes("Init") if meta else self.passes("Init")

    def kept(self, mod: str) -> bool:
        """Whether every importer must keep reading `mod` as it does: a module
        of a dependency, or one with side effects."""
        if mod not in self.keep_cache:
            if not self.project(mod):
                self.keep_cache[mod] = True
                return True
            code = lean_source_evidence.code_only(self.text(mod))
            self.keep_cache[mod] = ("keep-downstream" in module_annotations(self.text(mod))
                                   or bool(SIDE_EFFECTS.search(code)) or bool(INSTANCE_DECLS.search(code))
                                   or bool(INITIALIZER_DECLS.search(code)))
        return self.keep_cache[mod]


def prepare_effects(graph: Graph, modules, uses) -> None:
    """Batch registry metadata whose uses can disappear during elaboration."""
    if uses is None:
        return
    todo = sorted({m for m in modules if m not in graph.effect_checked and graph.project(m) and not graph.kept(m)})
    if not todo:
        return
    effects = uses(todo, "effects")
    for m in todo:
        opaque = effects.get(m, set()) - STRUCTURAL_EXTENSIONS
        if opaque:
            graph.keep_cache[m] = True
            graph.opaque_extensions[m] = sorted(opaque)
        graph.effect_checked.add(m)

def graph_path(mod: str) -> pathlib.Path:
    """The source of a module of the project."""
    return LEAN / pathlib.Path(*mod.split(".")).with_suffix(".lean")


def build_modules(mods: list[str], timeout: float | None = None) -> None:
    """Build `mods` (Lake skips what is up to date), or stop: shake reads
    their `.olean`s."""
    if not mods:
        return
    progress(f"building {len(mods)} modules (what is up to date is skipped)")
    log = LEAN / ".lake/import-analysis" / f"{time.time_ns()}.log"
    records = []
    try:
        failing = build_failures(mods, timeout=timeout, phase="analysis", log=log, attempts=records)
        if failing:
            raise SystemExit(f"the modules do not build; fix that first: {', '.join(sorted(failing))}; see {log}")
    finally:
        lean_import_build.save(log.with_suffix(".json"), {"attempts": records})


def shake(mods: list[str], *, built: bool = False, timeout: float | None = None) -> str:
    """`lake shake`'s suggestions for `mods`, built first."""
    if not built:
        build_modules(mods, timeout)
    # Shake reads the private parts of the modules and of all they import,
    # which a build restored with `--empty-private` leaves empty.
    if lean_cache.fill_private(LEAN, mods):
        progress("wrote the private parts shake reads")
    progress(f"lake shake on {len(mods)} modules")
    args = ["lake", "--no-ansi", "shake", "--force"]
    for m in mods:
        args += ["--only", m]
    log = LEAN / ".lake/import-analysis" / f"{time.time_ns()}-shake.log"
    attempt = lean_import_build.Attempt("shake", mods, str(log))
    valid = False
    try:
        lean_import_build.command(args + mods, LEAN, log, attempt, 120 if timeout is None else timeout)
        if attempt.timed_out:
            raise TimeoutError(f"lake shake timed out; Lean processes stopped; see {log}")
        output = log.read_text()
        # Shake exits 1 when it has suggestions. That is a valid analysis
        # outcome, distinct from a successful proof-verification build.
        if (attempt.returncode not in (0, 1) or "error:" in output
                or (attempt.returncode and not suggestions(output))):
            raise SystemExit(f"lake shake failed (exit {attempt.returncode}); see {log}")
        valid = True
        return output
    except BaseException as error:
        if attempt.error is None:
            attempt.error = f"{type(error).__name__}: {error}"
        raise
    finally:
        lean_import_build.save(log.with_suffix(".json"), {**attempt.json(), "valid_suggestions": valid})


_T0 = time.time()


def progress(msg: str) -> None:
    """A phase, with the time since the start, on stderr (the findings go
    there too, after)."""
    print(f"[{time.time() - _T0:6.1f} s] {msg}", file=sys.stderr, flush=True)


def read_declarations(mods: list[str], view: str, timeout: float | None = 120) -> dict:
    """Run the reader with the same cancellation guarantees as proof builds."""
    log = LEAN / ".lake/import-analysis" / f"{time.time_ns()}-reader-{view}.log"
    attempt = lean_import_build.Attempt("reader", mods, str(log))
    try:
        lean_import_build.command(
            ["lake", "env", "lean", "--run", str(ROOT / "ci/lean_module_uses.lean"), view, *mods],
            LEAN, log, attempt, timeout)
        if attempt.timed_out:
            raise TimeoutError(f"declaration reader exceeded {timeout}s; Lean processes stopped; see {log}")
        if not attempt.succeeded:
            raise RuntimeError(f"declaration reader exited {attempt.returncode}; see {log}")
        try:
            data = json.loads(log.read_text())
        except ValueError as error:
            raise ValueError(f"invalid declaration reader output; see {log}") from error
        valid = isinstance(data, dict) and set(data) == set(mods)
        if valid and view == "both":
            valid = all(isinstance(row, dict) and set(row) == set(DECLARATION_VIEWS)
                        and all(isinstance(xs, list) and all(isinstance(x, str) for x in xs) for xs in row.values())
                        for row in data.values())
        elif valid:
            valid = all(isinstance(xs, list) and all(isinstance(x, str) for x in xs) for xs in data.values())
        if not valid:
            raise ValueError(f"incomplete declaration evidence from Lean; see {log}")
        return data
    except BaseException as error:
        if attempt.error is None:
            attempt.error = f"{type(error).__name__}: {error}"
        raise
    finally:
        lean_import_build.save(log.with_suffix(".json"), {"view": view, **attempt.json()})


def module_uses(mods: list[str], view: str) -> dict[str, set[str]]:
    """The modules each of `mods` uses (`ci/lean_module_uses.lean`, which
    reads their builds): `public`, what Lean checks as public uses (statements
    and exposed bodies, with the proofs elaborated as part of them); `private`,
    everything."""
    if not mods:
        return {}
    if view in ("references", "namespaces"):
        result = {}
        for mod in mods:
            data = lean_source_evidence.read(LEAN, mod, header(graph_path(mod).read_text()))
            result[mod] = (lean_source_evidence.references(data) if view == "references"
                           else lean_source_evidence.namespaces(data))
        return result
    if view in DECLARATION_VIEWS:
        return {m: values[view] for m, values in module_evidence(mods).items()}
    progress(f"reading {len(mods)} modules' {view} uses")
    return {m: set(us) for m, us in read_declarations(mods, view).items()}


def module_evidence(mods: list[str], timeout: float | None = 120) -> dict[str, dict[str, set[str]]]:
    """Load each module once for both public and private declaration evidence."""
    if not mods:
        return {}
    progress(f"reading {len(mods)} modules' public and private uses together")
    data = read_declarations(mods, "both", timeout)
    return {m: {view: set(us) for view, us in row.items()} for m, row in data.items()}


def suggestions(text: str) -> dict[str, tuple[list[str], list[str]]]:
    """Of `lake shake`'s output, the imports it would remove and add, per
    file (as `public import X`, `meta import X`, …)."""
    out = {}
    for f, body in re.findall(r"^(\S+\.lean):\n((?:  .*\n)*)", text, re.M):
        rem, add = [], []
        for line in body.splitlines():
            m = re.match(r"\s*(remove|add) #\[(.*)\]", line)
            if m:
                (rem if m.group(1) == "remove" else add).extend(x.strip() for x in m.group(2).split(",") if x.strip())
        out[f] = (rem, add)
    return out


def shake_path(name: str) -> pathlib.Path:
    """Shake runs in LEAN, so its relative output paths are relative to that."""
    path = pathlib.Path(name)
    return (path if path.is_absolute() else LEAN / path).resolve()


def new_imports(mod: str, base: str | None, public: bool, meta: bool = False) -> set[str] | None:
    """The modules `mod` imports (publicly, or plainly) but did not so at the
    git revision `base` (None: every one, without a base or for a new file).
    Execution phases are compared separately."""
    if base is None:
        return None
    rel = pathlib.Path("lean", *mod.split(".")).with_suffix(".lean").as_posix()
    old = subprocess.run(["git", "-C", str(ROOT), "show", f"{base}:{rel}"], capture_output=True, text=True)
    if old.returncode:
        return None
    path = LEAN / pathlib.Path(*mod.split(".")).with_suffix(".lean")
    was = {i for i, p, me, _ in header(old.stdout) if p == public and me == meta}
    return {i for i, p, me, _ in header(path.read_text()) if p == public and me == meta} - was


def new_public(mod: str, base: str | None) -> set[str] | None:
    """The modules `mod` imports publicly but did not at `base`."""
    return new_imports(mod, base, True)


def new_plain(mod: str, base: str | None) -> set[str] | None:
    """The modules `mod` imports plainly but did not at `base`."""
    return new_imports(mod, base, False)


def new_meta(mod: str, base: str | None) -> set[str] | None:
    """The private meta imports added since `base`."""
    return new_imports(mod, base, False, True)


class Demoted(Graph):
    """`graph`, but for the modules of `pairs` importing those privately:
    `Demoted(graph, mod, x)`, or `Demoted(graph, pairs={(mod, x), …})`."""

    def __init__(self, graph: Graph, mod: str | None = None, x: str | None = None, pairs=None):
        super().__init__(graph.roots)
        self.graph = graph
        self.files, self.texts = graph.files, graph.texts
        self.pairs = set(pairs or ()) | ({(mod, x)} if mod is not None else set())
        self.ordinary_changed = {m for m, _ in self.pairs}
        self.public_changed = set(self.ordinary_changed)

    def reuse_passes(self, mod: str) -> frozenset[str] | None:
        original = self.graph.passes(mod)
        return original if self.ordinary_changed.isdisjoint(original) else None

    def reuse_meta_exports(self, mod: str) -> frozenset[str] | None:
        original = self.graph.meta_exports(mod)
        unchanged = (self.public_changed.isdisjoint(original)
                     and self.public_changed.isdisjoint(self.graph.passes(mod)))
        return original if unchanged else None

    def imports(self, mod: str) -> list[tuple[str, bool, bool, bool]]:
        imps = self.graph.imports(mod)
        return [(i, p and (me or (mod, i) not in self.pairs), me, a) for i, p, me, a in imps]


class Planned(Demoted):
    """Visibility of the whole edit batch, including repairs and removals."""

    def __init__(self, graph: Graph, edits: list[Edit]):
        super().__init__(graph, pairs={(e.module, e.dependency) for e in edits if e.action == "demote"})
        self.removed: dict[str, set[tuple[str, bool, bool]]] = {}
        self.added: dict[str, list[Edit]] = {}
        for e in edits:
            if e.action in ("remove", "remove_public", "remove_meta"):
                self.removed.setdefault(e.module, set()).add((e.dependency, e.action == "remove_public",
                                                            e.action.endswith("_meta")))
                if e.action == "remove_public":
                    self.ordinary_changed.add(e.module)
                    self.public_changed.add(e.module)
            elif e.action.startswith("add"):
                self.added.setdefault(e.module, []).append(e)
                if e.action.startswith("add_public"):
                    self.public_changed.add(e.module)
                    if not e.action.endswith("_meta"):
                        self.ordinary_changed.add(e.module)

    def imports(self, mod: str) -> list[tuple[str, bool, bool, bool]]:
        removed = self.removed.get(mod, set())
        imps = [(i, p, me, a) for i, p, me, a in super().imports(mod) if (i, p, me) not in removed or a]
        for e in self.added.get(mod, []):
            imps.append((e.dependency, e.action.startswith("add_public"), e.action.endswith("_meta"), False))
        return imps


def reads(graph: Graph, mod: str) -> set[str]:
    """What `mod` sees: what it imports, and what those pass on."""
    return set(graph.reads(mod))


def preserve_forwarding(graph: Graph, edits: list[Edit], modules: list[str], uses=None) -> None:
    """Preserve unknown effects in the same execution phase as before."""
    for mod in modules:
        for meta in (False, True):
            planned = Planned(graph, edits)
            before = graph.meta_exports(mod) if meta else graph.passes(mod)
            after = planned.meta_exports(mod) if meta else planned.passes(mod)
            prepare_effects(graph, before - after, uses)
            keep = {x for x in before - after if graph.kept(x)}
            coverage = planned.meta_passes if meta else planned.passes
            keep = {x for x in keep if not any(x != y and x in coverage(y) for y in keep)}
            edits.extend(Edit(mod, "add_public_meta" if meta else "add_public", x) for x in sorted(keep))


def analyze(mods: list[str], shaken: dict[str, tuple[list[str], list[str]]], graph: Graph,
             new: dict[str, set[str] | None] | None = None, plain: dict[str, set[str] | None] | None = None,
             uses=None, library: list[str] | None = None, protected: set[tuple[str, str]] | None = None,
             meta_plain: dict[str, set[str] | None] | None = None,
             keep_private: set[tuple[str, str]] | None = None) -> Plan:
    """What to change, for each of `mods`:

    * a `public import` of a module of the project that `lake shake`
      (`shaken`) finds used only privately, of those the change made public
      (`new`, by module; all of them where None), unless what Lean checks as
      public uses it (`uses(mods, "public")`: proofs inside exposed definitions,
      which shake counts as private), naming the modules of `library` that
      used what it passed on (`uses(mods, "private")`), which must import it
      themselves;
    * a plain import of a module of the project that shake finds unused, of
      those the change added (`plain`; all of them where None).
    """
    # Pass 1: shake's candidates, per module.
    found = []  # (mod, rel, lines, private, unused)
    decisions = {}

    def decide(mod, dependency, action, status, reason, **evidence):
        meta, all_ = evidence.pop("meta", False), evidence.pop("import_all", False)
        decisions[mod, dependency, action, meta, all_] = dict(
            module=mod, dependency=dependency, action=action, meta=meta, import_all=all_,
            status=status, reason=reason, evidence=evidence)

    protected = protected or set()
    keep_private = keep_private or set()
    prepare_effects(graph, {x for m in mods for x, _, _, _ in header(graph.text(m))}, uses)
    for mod in mods:
        path = graph.path(mod)
        rel = f"lean/{path.relative_to(LEAN)}"
        rem, add = next((v for f, v in shaken.items() if shake_path(f) == path.resolve()), ([], []))
        lines = graph.text(mod).splitlines()
        annotations = module_annotations(graph.text(mod))
        pinned = {m.group(4) for n, s in header_lines(lines)
                  if (m := IMPORT.fullmatch(s)) and "shake: keep" in lines[n]}
        for x, public, meta, all_ in header(graph.text(mod)):
            if not graph.project(x):
                continue
            action = "demote" if public else "remove_meta" if meta else "remove"
            selected = new if public else meta_plain if meta else plain
            status, reason = "not_considered", "not_hypothesized"
            if (meta and public) or all_:
                status, reason = "unsupported", "meta_or_import_all"
            elif "keep-all" in annotations:
                status, reason = "retained", "module_keep_all"
            elif x in pinned:
                status, reason = "retained", "import_keep"
            elif graph.kept(x):
                status, reason = "retained", "opaque_module_effects"
            elif (mod, x) in protected:
                status, reason = "deferred", "protected_importer"
            elif not public and not meta and (mod, x) in keep_private:
                status, reason = "retained", "initialization_order_anchor"
            elif (selected or {}).get(mod) is not None and x not in selected[mod]:
                status, reason = "not_considered", "outside_selected_diff"
            evidence = {}
            if reason == "opaque_module_effects" and x in graph.opaque_extensions:
                evidence["extensions"] = graph.opaque_extensions[x]
            if reason == "not_hypothesized" and (retained := getattr(shaken, "retained", {}).get((mod, x, action))):
                status, reason = "retained", retained
                evidence["modules"] = [x]
            decide(mod, x, action, status, reason, meta=meta, import_all=all_, **evidence)
        if "keep-all" in annotations:
            continue
        public_after = {x.split()[-1] for x in add if x.startswith("public import ")}
        added_after = {x.split()[-1] for x in add if not x.startswith("meta ") and " meta " not in x}
        made = (new or {}).get(mod)
        private = sorted(
            x.split()[-1] for x in rem
            if re.fullmatch(r"public import \S+", x) and x.split()[-1] not in public_after
            and graph.project(x.split()[-1]) and not graph.kept(x.split()[-1])
            and (made is None or x.split()[-1] in made)
        )
        added = (plain or {}).get(mod)
        unused = sorted(
            x.split()[-1] for x in rem
            if re.fullmatch(r"import \S+", x) and x.split()[-1] not in added_after
            and graph.project(x.split()[-1]) and not graph.kept(x.split()[-1])
            and (added is None or x.split()[-1] in added)
        )
        # Enforce keep locally too: shake output may be captured, stale or
        # supplied by an independent candidate generator.
        actual = set(header(graph.text(mod)))
        private = [x for x in private if x not in pinned and (mod, x) not in protected
                   and (x, True, False, False) in actual]
        unused = [x for x in unused if x not in pinned and (mod, x) not in protected
                  and (mod, x) not in keep_private
                  and (x, False, False, False) in actual]
        for x in private:
            decide(mod, x, "demote", "proposed", "shake_hypothesis")
        for x in unused:
            decide(mod, x, "remove", "proposed", "shake_hypothesis")
        if private or unused:
            found.append((mod, rel, graph.text(mod).split("\n"), private, unused))
    # Pass 2: what Lean checks as public uses, for every module with a
    # candidate at once (proofs inside exposed definitions count).
    own_meta = {}
    if uses is not None:
        pub = uses([f[0] for f in found if f[3]], "public") if any(f[3] for f in found) else {}
        meta_pub = uses([f[0] for f in found if f[3]], "meta_public") if any(f[3] for f in found) else {}
        kept_found = []
        for mod, rel, lines, private, unused in found:
            direct = {i for i, p, meta, _ in graph.imports(mod) if p and not meta}
            direct_meta = {i for i, p, meta, _ in graph.imports(mod) if p and meta}
            used = pub.get(mod, set())
            # A module imports directly what it uses (CLAUDE.md): it keeps
            # `public import X` if it publicly uses X itself; otherwise X
            # becomes a plain import, and the module imports publicly, itself,
            # what it publicly used of what X passed on. Each finding depends
            # only on the module's own uses and imports: they hold together.
            demote = []
            for x in private:
                if x in used:
                    decide(mod, x, "demote", "retained", "public_declaration_dependency", modules=[x])
                    continue
                need = {y for y in used & graph.passes(x) if y not in direct} - graph.implicit_reads(mod)
                need = {y for y in need if not any(y != z and y in graph.passes(z) for z in need)}
                meta_need = ((meta_pub.get(mod, set()) & graph.meta_exports(x)) - direct_meta
                             - graph.implicit_reads(mod, True))
                meta_need = {y for y in meta_need if not any(y != z and y in graph.meta_passes(z) for z in meta_need)}
                own_meta[mod, x] = sorted(meta_need)
                demote.append((x, sorted(need)))
                decide(mod, x, "demote", "proposed", "no_direct_public_dependency",
                       public_repairs=sorted(need), meta_repairs=sorted(meta_need))
            kept_found.append((mod, rel, lines, demote, unused))
        found = kept_found
    else:
        found = [(mod, rel, lines, [(x, []) for x in private], unused) for mod, rel, lines, private, unused in found]
    # Start with the demotions and their own public repairs, including
    # preserved effects. Candidate removals are checked against this whole
    # graph, in a stable greedy order, without circular justifications.
    base = []
    for mod, _, _, private, _ in found:
        for x, need in private:
            base.append(Edit(mod, "demote", x))
            base.extend(Edit(mod, "add_public", y) for y in need)
            base.extend(Edit(mod, "add_public_meta", y) for y in own_meta.get((mod, x), []))
    preserve_forwarding(graph, base, [m for m, _, _, private, _ in found if private], uses)
    local_repairs, replacement_repairs = [], {}
    if uses is not None:
        # The repairs may make a newly demoted import unnecessary locally as
        # well. Check its removal in this same transaction instead of paying
        # for a second proof rebuild in the next round.
        own_private = uses([m for m, _, _, private, _ in found if private], "private") if any(f[3] for f in found) else {}
        found = [(m, rel, lines, private, sorted(set(unused) | {
            x for x, _ in private if x not in own_private.get(m, set()) and (m, x) not in keep_private}))
                 for m, rel, lines, private, unused in found]
    if uses is not None and any(f[4] for f in found):
        proposed = [Edit(m, "remove", x) for m, _, _, _, unused in found for x in unused]
        worst = Planned(graph, base + proposed)
        provided = {m: {y for y in ((graph.reads(m) - worst.reads(m)) |
                                   (graph.reads(m, True) - worst.reads(m, True))) if graph.project(y)}
                    for m, _, _, _, unused in found if unused}
        prepare_effects(graph, set().union(*provided.values()), uses)
        targets = sorted(provided)
        recorded = uses(targets, "private")
        recorded_meta = uses(targets, "meta_private")
        indexed = uses(targets, "references")
        fallback = any(m not in indexed for m in targets)
        names = uses(sorted(set().union(*provided.values())), "names") if provided and fallback else {}
        context = {y for m in targets for y in graph.reads(m) | graph.reads(m, True) if graph.project(y)}
        namespaces = uses(sorted(context), "namespaces") if context else {}
        unindexed = {m for m in targets if unindexed_namespace_opens(graph.text(m), namespaces)}
        read_namespace_exports(graph, set().union(*(provided[m] for m in unindexed)), uses)
        accepted = []
        kept_found = []
        for mod, rel, lines, private, unused in found:
            removable = []
            opened = opened_namespaces("\n".join(lines))
            for x in unused:
                if x in recorded.get(mod, set()) or x in indexed.get(mod, set()):
                    decide(mod, x, "remove", "retained", "direct_dependency", modules=[x])
                    continue
                after = Planned(graph, base + accepted + [Edit(mod, "remove", x)])
                lost = graph.reads(mod) - after.reads(mod)
                lost_meta = graph.reads(mod, True) - after.reads(mod, True)
                # Narrow a provider to the declarations actually consumed
                # through it, preserving the original execution phase. Exact
                # index references supplement proof terms, not suffix guesses.
                ordinary = lost & (recorded.get(mod, set()) | indexed.get(mod, set()))
                meta = lost_meta & (recorded_meta.get(mod, set()) | indexed.get(mod, set()))
                repairs = [Edit(mod, "add", y) for y in sorted(ordinary)] + [
                    Edit(mod, "add_meta", y) for y in sorted(meta)]
                if repairs:
                    after = Planned(graph, base + accepted + [Edit(mod, "remove", x)] + repairs)
                    if (not after.reads(mod) <= graph.reads(mod)
                            or not after.reads(mod, True) <= graph.reads(mod, True)):
                        decide(mod, x, "remove", "retained", "replacement_would_expand_visibility")
                        continue
                    lost = graph.reads(mod) - after.reads(mod)
                    lost_meta = graph.reads(mod, True) - after.reads(mod, True)
                if any(graph.kept(y) for y in lost | lost_meta):
                    decide(mod, x, "remove", "retained", "opaque_transitive_effects",
                           modules=sorted(y for y in lost | lost_meta if graph.kept(y)))
                    continue
                if lost & recorded.get(mod, set()) or lost_meta & recorded_meta.get(mod, set()):
                    decide(mod, x, "remove", "retained", "private_declaration_dependency",
                           ordinary=sorted(lost & recorded.get(mod, set())),
                           meta=sorted(lost_meta & recorded_meta.get(mod, set())))
                    continue
                source = source_needs_with_exports(graph, after, mod,
                                                  {y for y in lost | lost_meta if graph.project(y)},
                                                  names, indexed.get(mod), namespaces, uses)
                if not source:
                    removable.append(x)
                    accepted.append(Edit(mod, "remove", x))
                    accepted.extend(repairs)
                    local_repairs.extend(repairs)
                    replacement_repairs[mod, x] = repairs
                    decide(mod, x, "remove", "proposed", "replace_private_provider" if repairs else "no_recorded_dependency",
                           source_index=mod in indexed, private_repairs=sorted(ordinary), private_meta_repairs=sorted(meta))
                else:
                    decide(mod, x, "remove", "retained", "source_dependency", modules=sorted(source),
                           source_index=mod in indexed)
            kept_found.append((mod, rel, lines, private, removable))
        found = kept_found
    plan = Plan(edits=list(base) + local_repairs)
    plan.edits.extend(Edit(mod, "remove", x) for mod, _, _, _, unused in found for x in unused)
    narrow_private_meta(plan, mods, shaken, graph, uses, decide, meta_plain, protected)
    narrow_dependencies(plan, mods, shaken, graph, decide, new, plain, protected)
    meta_messages = list(plan.messages)

    # Compute losses against ALL demotions and additions at once. A pair of
    # paths can each look redundant when considered in isolation.
    losing, read_losing, meta_read_losing, public_losing, meta_public_losing = {}, {}, {}, {}, {}
    used, public_used, meta_used, meta_public_used = {}, {}, {}, {}
    planned = Planned(graph, plan.edits)
    if uses is not None and library:
        sources = {e.module for e in plan.edits if e.action in NARROWING}
        everyone = sorted(set().union(*(graph.importers(m, library) for m in sources)))
        for j in everyone:
            read_losing[j] = graph.reads(j) - planned.reads(j)
            meta_read_losing[j] = graph.reads(j, True) - planned.reads(j, True)
            public_losing[j] = graph.passes(j) - planned.passes(j)
            meta_public_losing[j] = graph.meta_exports(j) - planned.meta_exports(j)
            gone = {y for y in (read_losing[j] | meta_read_losing[j] |
                               public_losing[j] | meta_public_losing[j]) if graph.project(y)}
            if gone:
                losing[j] = gone
        if losing:
            public_used = uses(sorted(losing), "public")
            used = uses(sorted(losing), "private")
            meta_public_used = uses(sorted(losing), "meta_public")
            meta_used = uses(sorted(losing), "meta_private")
            indexed = uses(sorted(losing), "references")
            fallback = any(j not in indexed for j in losing)
            names = uses(sorted(set().union(*losing.values())), "names") if fallback else {}
            context = {y for j in losing for y in graph.reads(j) | graph.reads(j, True) if graph.project(y)}
            namespaces = uses(sorted(context), "namespaces") if context else {}
            unindexed = {j for j in losing if unindexed_namespace_opens(graph.text(j), namespaces)}
            read_namespace_exports(graph, set().union(*(losing[j] for j in unindexed)), uses)
            for j, gone in losing.items():
                source = source_needs_with_exports(graph, planned, j, gone, names, indexed.get(j), namespaces, uses)
                for y in sorted(gone):
                    if y in public_used.get(j, set()) and y in read_losing[j] | public_losing[j]:
                        plan.edits.append(Edit(j, "add_public", y))
                    elif y in read_losing[j] and (y in used.get(j, set()) or y in source):
                        plan.edits.append(Edit(j, "add", y))
                    if y in meta_public_used.get(j, set()) and y in meta_read_losing[j] | meta_public_losing[j]:
                        plan.edits.append(Edit(j, "add_public_meta", y))
                    elif y in meta_read_losing[j] and (y in meta_used.get(j, set()) or y in source):
                        plan.edits.append(Edit(j, "add_meta", y))
                used[j] = used.get(j, set()) | source
    removed_public = {(m, x) for m, _, _, private, unused in found for x, _ in private if x in unused}
    out = []
    for mod, rel, lines, private, unused in found:
        imps = graph.imports(mod)
        if private:
            names = [x for x, _ in private]
            before = set().union(*(graph.passes(i) for i, p, _, _ in imps if p))
            after = set().union(*(graph.passes(i) for i, p, _, _ in imps if p and i not in names))
            lost = {x for x in before - after if graph.kept(x)}
            keep = sorted(x for x in lost if not any(x in graph.passes(y) for y in lost if y != x))
            for x, need in private:
                n = next(i for i, s in header_lines(lines)
                         if (m := IMPORT.fullmatch(s)) and m.group(4) == x and m.group(1) and not m.group(2)) + 1
                if (mod, x) in removed_public:
                    msg = f"{rel}:{n}: `public import {x}`: no recorded local use remains after repairs: remove it"
                else:
                    msg = f"{rel}:{n}: `public import {x}`: {mod} uses it only privately: make it `import {x}`"
                    if (mod, x) in keep_private:
                        msg = (f"{rel}:{n}: `public import {x}`: make it `import {x}`; "
                               "retain the private provider to preserve initialization order")
                if need:
                    msg += ", import publicly itself what it used through it: " + ", ".join(f"`public import {y}`" for y in need)
                if replacement_repairs.get((mod, x)):
                    msg += ", import directly for its private uses: " + ", ".join(
                        f"`{'meta ' if e.action == 'add_meta' else ''}import {e.dependency}`" for e in replacement_repairs[mod, x])
                if uses is None or not library:
                    msg += f", and import it where the modules importing {mod} use it"
                else:
                    users = {}
                    for j, gone in losing.items():
                        need = gone & (used.get(j, set()) | public_used.get(j, set()))
                        if need:
                            users[j] = need
                    if users:
                        msg += ", and import what it passed on where it is used: " + "; ".join(
                            f"{j} uses {', '.join(sorted(need))}" for j, need in sorted(users.items()))
                out.append(msg)
            if keep:
                out.append(f"{rel}: and keep passing on what those passed on that "
                           f"the check cannot see the uses of: " + ", ".join(f"`public import {x}`" for x in keep))
        for x in unused:
            n = next((i for i, s in header_lines(lines)
                      if (m := IMPORT.fullmatch(s)) and m.group(4) == x and not m.group(1) and not m.group(2)), None)
            if n is not None:
                message = f"{rel}:{n + 1}: `import {x}`: {mod} does not use it: remove it"
                if replacement_repairs.get((mod, x)):
                    message += ", import what it used through it: " + ", ".join(
                        f"`{'meta ' if e.action == 'add_meta' else ''}import {e.dependency}`" for e in replacement_repairs[mod, x])
                out.append(message)
    plan.messages = out + meta_messages
    if removed_public:
        plan.edits = [e for e in plan.edits if not ((e.module, e.dependency) in removed_public
                                                   and e.action in ("demote", "remove"))]
        plan.edits.extend(Edit(m, "remove_public", x) for m, x in sorted(removed_public))
        plan.edits.extend(Edit(m, "remove", x) for m, x in sorted(removed_public)
                          if any(i == x and not p and not meta and not all_ for i, p, meta, all_ in graph.imports(m)))
        for m, x in removed_public:
            decision = decisions.pop((m, x, "remove", False, False))
            demotion = decisions.pop((m, x, "demote", False, False))
            decision.update(action="remove_public", reason="no_local_dependency_after_repairs")
            decision["evidence"].update({k: v for k, v in demotion["evidence"].items() if k.endswith("repairs")})
            decisions[m, x, "remove_public", False, False] = decision
    plan.decisions = [decisions[k] for k in sorted(decisions)]
    plan.edits = sorted(set(plan.edits))
    discipline_guards = import_discipline_guards(plan, graph, library or [])
    if discipline_guards.keys() - protected:
        remaining = analyze(mods, shaken, graph, new, plain, uses, library,
                            protected | discipline_guards.keys(), meta_plain, keep_private)
        for pair, repairs in discipline_guards.items():
            if pair in protected:
                continue
            remaining.deferred.append({"module": pair[0], "dependency": pair[1],
                                       "reason": "would require an import forbidden by repository discipline",
                                       "invalid_repairs": repairs})
            for decision in remaining.decisions:
                if (decision["module"], decision["dependency"]) == pair and decision["status"] == "deferred":
                    decision["reason"] = "import_discipline_boundary"
                    decision["evidence"]["invalid_repairs"] = repairs
        return remaining
    repair_users = {e.module for e in plan.edits if e.action.startswith("add")}
    reviewed_users = {m for m in repair_users if reviewed(m)}
    kept_users = {m for m in repair_users if "keep-all" in module_annotations(graph.text(m))}
    protected_users = reviewed_users | kept_users
    if protected_users and library:
        # Preserve only the boundaries whose narrowing would require
        # editing reviewed or explicitly kept files. Replan the rest; never strand their repairs
        # or block independent work elsewhere in the library.
        guarded_edits = {e for e in plan.edits if e.action in NARROWING
                         and graph.importers(e.module, library) & protected_users}
        guarded = {(e.module, e.dependency) for e in guarded_edits}
        if guarded - protected:
            remaining = analyze(mods, shaken, graph, new, plain, uses, library,
                                protected | guarded, meta_plain, keep_private)
            remaining.deferred.extend({"module": e.module, "dependency": e.dependency, "action": e.action,
                                       "reason": "would require editing a protected importer",
                                       "reviewed_importers": sorted(graph.importers(e.module, library) & reviewed_users),
                                       "kept_importers": sorted(graph.importers(e.module, library) & kept_users)}
                                      for e in sorted(guarded_edits) if (e.module, e.dependency) not in protected)
            return remaining
    plan.exclude_reviewed()
    if not plan.blocked and uses is not None and plan.edits:
        order_guards = initialization_order_guards(plan, graph, library or [], uses)
        if order_guards:
            anchors = {pair for pair in order_guards if any(
                (e.module, e.dependency) == pair and e.action == "remove_public" for e in plan.edits)} - keep_private
            blocked = set(order_guards) - anchors
            remaining = analyze(mods, shaken, graph, new, plain, uses, library,
                                protected | blocked, meta_plain, keep_private | anchors)
            for pair, details in order_guards.items():
                remaining.deferred.append({"module": pair[0], "dependency": pair[1],
                                           "reason": ("would remove opaque initialization" if details.get("lost_opaque_providers")
                                                      else "would reorder opaque initialization"),
                                           "private_anchor_retained": pair in anchors, **details})
                for decision in remaining.decisions:
                    if (decision["module"], decision["dependency"]) == pair:
                        if decision["status"] == "deferred":
                            decision["reason"] = "opaque_initialization_order"
                        if pair in anchors and decision["action"] == "demote":
                            decision["evidence"]["private_initialization_anchor"] = True
            return remaining
    return plan


def import_discipline_guards(plan: Plan, graph: Graph, library: list[str]) -> dict:
    """A compiling repair must also obey target and trusted-layer boundaries.

    Infer TCB subdirectories from the complete library identities, the same
    directories check_lean_imports uses as targets. This remains portable replay
    evidence and needs no extra access to the original checkout.
    """
    targets = {parts[2] for mod in library if len(parts := mod.split(".")) > 3
               and parts[:2] == [LIBRARY, "TCB"]}
    invalid = []
    for edit in plan.edits:
        if not edit.action.startswith("add"):
            continue
        parts = edit.module.split(".")[1:]
        own = import_discipline.target_of(parts, targets)
        other = import_discipline.target_of(edit.dependency.split(".")[1:], targets)
        layer = parts[0] if parts else ""
        allowed = import_discipline.ALLOWED_IMPORTS.get(layer)
        reason = None
        if own and other and own != other:
            reason = f"a module of {own} may not import a module of {other}"
        elif allowed and not import_discipline.allowed(edit.dependency, allowed):
            reason = f"{layer}/ may not import {edit.dependency}"
        if reason:
            invalid.append({**asdict(edit), "reason": reason})
    if not invalid:
        return {}
    guarded = {}
    for edit in plan.edits:
        if edit.action not in NARROWING:
            continue
        consumers = {edit.module} | (graph.importers(edit.module, library) if library else set())
        provided = set(graph.load_order(edit.dependency))
        repairs = [repair for repair in invalid if repair["module"] in consumers
                   and repair["dependency"] in provided]
        if repairs:
            guarded[edit.module, edit.dependency] = repairs
    return guarded


def initialization_order_guards(plan: Plan, graph: Graph, library: list[str], uses) -> dict:
    """Preserve order around registries, even if the same modules stay readable.

    Reordering instances can change definition values while type checking still
    succeeds. Preserve relative order among opaque providers; structural
    bookkeeping alone does not impose an initialization-order boundary.
    """
    primary = [e for e in plan.edits if e.action in NARROWING]
    scopes = {e.module: {e.module} | (graph.importers(e.module, library) if library else set()) for e in primary}
    targets = sorted(set().union(*scopes.values()))
    after = Planned(graph, plan.edits)
    changed = []
    removed = []
    for mod, ordinary_only in ((mod, phase) for mod in targets for phase in (False, True)):
        old, new = graph.load_order(mod, ordinary_only), after.load_order(mod, ordinary_only)
        lost = {m for m in set(old) - set(new) if graph.project(m)}
        if lost:
            removed.append((mod, lost))
        common = set(old) & set(new)
        old, new = [m for m in old if m in common], [m for m in new if m in common]
        different = [i for i, (a, b) in enumerate(zip(old, new)) if a != b]
        if different:
            start, end = different[0], different[-1] + 1
            changed.append((mod, old[start:end], new[start:end]))
    prepare_effects(graph, {m for _, old, new in changed for m in old + new}
                    | {m for _, lost in removed for m in lost}, uses)
    guarded = {}
    for mod, lost in removed:
        opaque = {m for m in lost if graph.kept(m)}
        if not opaque:
            continue
        for e in primary:
            if mod in scopes[e.module] and opaque & set(graph.load_order(e.dependency)):
                guarded[e.module, e.dependency] = {
                    "consumer": mod, "opaque_modules": sorted(opaque)[:20], "opaque_module_count": len(opaque),
                    "lost_opaque_providers": sorted(opaque)[:20], "original_order": [], "proposed_order": []}
    for mod, old, new in changed:
        opaque = {m for m in old + new if graph.kept(m)}
        old_opaque = [m for m in old if m in opaque]
        new_opaque = [m for m in new if m in opaque]
        if old_opaque == new_opaque:
            continue
        reaching = [e for e in primary if mod in scopes[e.module]]
        # Removing an import of a dependency's module (`narrow_dependencies`)
        # reorders that dependency's own modules: that is what it does. It
        # is held back only where it reorders the project's opaque modules.
        if ([m for m in old_opaque if graph.project(m)] == [m for m in new_opaque if graph.project(m)]):
            reaching = [e for e in reaching if not graph.dependency(e.dependency)]
            if not reaching:
                continue
        causes = [e for e in reaching if opaque & set(graph.load_order(e.dependency))] or reaching
        for e in causes:
            guarded[e.module, e.dependency] = {
                "consumer": mod, "opaque_modules": sorted(opaque)[:20], "opaque_module_count": len(opaque),
                "original_order": old_opaque[:20], "proposed_order": new_opaque[:20]}
    return guarded


def narrow_private_meta(plan: Plan, mods: list[str], shaken: dict, graph: Graph, uses, decide,
                        selected: dict | None = None, protected: set[tuple[str, str]] | None = None) -> None:
    """Remove unused private meta edges against the complete ordinary plan.

    Meta imports grant execution access to regular definitions. An ordinary
    reference to the same module does not establish that this access is used,
    while resolved elaboration references remain a conservative phase-agnostic
    guard. Import-all consumers are repaired by the common downstream pass.
    """
    if uses is None:
        return
    candidates = {}
    for mod in mods:
        text = graph.text(mod)
        if "keep-all" in module_annotations(text):
            continue
        lines = text.splitlines()
        pinned = {m.group(4) for n, s in header_lines(lines)
                  if (m := IMPORT.fullmatch(s)) and "shake: keep" in lines[n]}
        rem, add = next((v for f, v in shaken.items() if shake_path(f) == graph.path(mod).resolve()), ([], []))
        hypothesized = {s.split()[-1] for s in rem if re.fullmatch(r"meta import \S+", s)}
        hypothesized -= {s.split()[-1] for s in add if re.fullmatch(r"meta import \S+", s)}
        if (selected or {}).get(mod) is not None:
            hypothesized &= selected[mod]
        deps = sorted({x for x, public, meta, all_ in header(text) if meta and not public and not all_
                       and x in hypothesized and x not in pinned and (mod, x) not in (protected or set())
                       and graph.project(x) and not graph.kept(x)})
        if deps:
            candidates[mod] = deps
    if not candidates:
        return
    targets = sorted(candidates)
    recorded = uses(targets, "meta_private")
    indexed = uses(targets, "references")
    worst = Planned(graph, plan.edits + [Edit(m, "remove_meta", x) for m, deps in candidates.items() for x in deps])
    # A meta import executes initializers behind PRIVATE dependencies too.
    # Keeping an ordinary occurrence does not preserve this execution access.
    hidden = {x: {y for y in graph.load_order(x) if graph.project(y)}
              for deps in candidates.values() for x in deps}
    prepare_effects(graph, {y for m in targets for y in graph.reads(m, True) - worst.reads(m, True)}
                    | {y for modules in hidden.values() for y in modules}, uses)
    for mod, deps in candidates.items():
        opened = opened_namespaces(graph.text(mod))
        before = Planned(graph, plan.edits)
        context = {y for y in before.reads(mod) | before.reads(mod, True) if graph.project(y)} if opened else set()
        namespaces = uses(sorted(context), "namespaces") if context else {}
        if unindexed_namespace_opens(graph.text(mod), namespaces):
            potential = {y for y in graph.reads(mod, True) - worst.reads(mod, True) if graph.project(y)}
            read_namespace_exports(graph, potential, uses)
        for x in deps:
            def decision(status, reason, **evidence):
                decide(mod, x, "remove_meta", status, reason, meta=True, **evidence)
            if x in recorded.get(mod, set()) or x in indexed.get(mod, set()):
                decision("retained", "direct_meta_or_source_dependency", modules=[x])
                continue
            hidden_opaque = {y for y in hidden[x] if graph.kept(y)}
            if hidden_opaque:
                decision("retained", "opaque_private_execution_effects", modules=sorted(hidden_opaque))
                continue
            before = Planned(graph, plan.edits)
            edit = Edit(mod, "remove_meta", x)
            after = Planned(graph, plan.edits + [edit])
            lost = before.reads(mod, True) - after.reads(mod, True)
            opaque = {y for y in lost if graph.kept(y)}
            if opaque:
                decision("retained", "opaque_transitive_meta_effects", modules=sorted(opaque))
                continue
            needed = lost & recorded.get(mod, set())
            if needed:
                decision("retained", "transitive_meta_dependency", modules=sorted(needed))
                continue
            project_lost = {y for y in lost if graph.project(y)}
            names = uses(sorted(project_lost), "names") if mod not in indexed and project_lost else {}
            source = source_needs_with_exports(graph, after, mod, project_lost, names,
                                              indexed.get(mod), namespaces, uses)
            if source:
                decision("retained", "source_dependency", modules=sorted(source), source_index=mod in indexed)
                continue
            plan.edits.append(edit)
            n = next(n for n, s in header_lines(graph.text(mod).splitlines())
                     if (m := IMPORT.fullmatch(s)) and m.group(4) == x and m.group(2)
                     and not m.group(1) and not m.group(3))
            rel = f"lean/{graph.path(mod).relative_to(LEAN)}"
            plan.messages.append(f"{rel}:{n + 1}: `meta import {x}`: no recorded meta or source use: remove it")
            decision("proposed", "no_recorded_meta_dependency", source_index=mod in indexed,
                     lost_meta_modules=len(lost))


def narrow_dependencies(plan: Plan, mods: list[str], shaken: dict, graph: Graph, decide,
                        public_selected: dict | None = None, plain_selected: dict | None = None,
                        protected: set[tuple[str, str]] | None = None) -> None:
    """Remove the imports of a dependency's modules (`graph.dependencies`)
    that `lake shake` finds unused.

    The other passes never touch a dependency's import: they cannot see what
    it changes for the importers (syntax, attributes, instances, simp sets).
    So a dependency's import accumulates in files that no longer use it, and
    with it the dependency's whole closure in every module importing them.
    Here shake's finding is only a hypothesis, which `fix_and_verify` keeps
    only if the module and every module importing it still build: a missing
    tactic or lemma fails the build; an attribute or instance that a proof
    needs fails it too. Where shake replaces such imports by a narrower
    module of the same dependency (e.g. three tactic modules by the one whose
    attribute the module uses), the replacement is added in the same edit.
    """
    if not graph.dependencies:
        return
    for mod in mods:
        text = graph.text(mod)
        if "keep-all" in module_annotations(text):
            continue
        lines = text.splitlines()
        pinned = {m.group(4) for n, s in header_lines(lines)
                  if (m := IMPORT.fullmatch(s)) and "shake: keep" in lines[n]}
        rem, add = next((v for f, v in shaken.items() if shake_path(f) == graph.path(mod).resolve()), ([], []))
        removed = {s.split()[-1]: s.startswith("public ") for s in rem
                   if re.fullmatch(r"(public )?import \S+", s) and graph.dependency(s.split()[-1])}
        added = {s.split()[-1]: s.startswith("public ") for s in add
                 if re.fullmatch(r"(public )?import \S+", s) and graph.dependency(s.split()[-1])}
        proposed = False
        rel = f"lean/{graph.path(mod).relative_to(LEAN)}"
        for x, public, meta, all_ in header(text):
            if meta or all_ or not graph.dependency(x) or removed.get(x) != public:
                continue
            action = "remove_public" if public else "remove"
            selected = (public_selected if public else plain_selected) or {}
            if x in pinned:
                decide(mod, x, action, "retained", "import_keep")
            elif (mod, x) in (protected or set()):
                decide(mod, x, action, "deferred", "protected_importer")
            elif selected.get(mod) is not None and x not in selected[mod]:
                decide(mod, x, action, "not_considered", "outside_selected_diff")
            else:
                n = next(n for n, s in header_lines(lines)
                         if (m := IMPORT.fullmatch(s)) and m.group(4) == x and bool(m.group(1)) == public
                         and not m.group(2) and not m.group(3))
                plan.edits.append(Edit(mod, action, x))
                plan.messages.append(f"{rel}:{n + 1}: `{'public ' if public else ''}import {x}`: "
                                     f"{mod} does not use this dependency's module: remove it")
                decide(mod, x, action, "proposed", "unused_dependency_module")
                proposed = True
        if proposed:
            for y, public in sorted(added.items()):
                plan.edits.append(Edit(mod, "add_public" if public else "add", y))
                plan.messages.append(f"{rel}: `{'public ' if public else ''}import {y}`: {mod} uses this "
                                     "narrower module of the dependency: import it instead")
                decide(mod, y, "add_public" if public else "add", "proposed", "narrower_dependency_module")


def problems(*args, **kwargs) -> list[str]:
    """Human diagnostics; use analyze() for the executable plan."""
    return analyze(*args, **kwargs).messages


WORD = re.compile(r"[^\W\d][\w'!?₀-₉]*")


def source_words(text: str) -> set[str]:
    """The identifiers' last components in a source, comments left out."""
    text = lean_source_evidence.code_only(text)
    return {w.rpartition(".")[2] for w in WORD.findall(text)}


OPEN = re.compile(r"^\s*(?:@\[[^\]\n]*\]\s*)?open\s+(?:scoped\s+)?([^\n]*)", re.M)
OPEN_TOKEN = re.compile(r"(?:«[^»]*»|[^\s«»()])+")


def opened_namespaces(text: str) -> set[str]:
    """The namespaces a source opens (`open A B`, `open A (x y)`), comments left out."""
    text = lean_source_evidence.code_only(text)
    return {ns for line in OPEN.findall(text) for ns in OPEN_TOKEN.findall(line)
            if ns[:1].isupper() or ns.startswith("«")}


def namespace_support(graph: Graph, mod: str, namespaces: dict[str, set[str]], opened: set[str]) -> set[str]:
    """Only queried opens matter; avoid repeatedly unioning every namespace."""
    if not opened:
        return set()
    providers = graph.reads(mod) | graph.reads(mod, True)
    return {ns for ns in opened if any(ns in namespaces.get(y, ()) for y in providers)}


def namespace_matches(space: str, opened: str) -> bool:
    return space == opened or space.endswith("." + opened) or space.startswith(opened + ".")


def unindexed_namespace_opens(text: str, namespaces: dict) -> set[str]:
    return {ns for ns in opened_namespaces(text)
            if not any(namespace_matches(space, ns) for spaces in namespaces.values() for space in spaces)}


def read_namespace_exports(graph: Graph, providers, uses) -> None:
    todo = sorted(set(providers) - graph.namespace_exports.keys())
    if todo and uses is not None:
        result = uses(todo, "namespace_exports")
        graph.namespace_exports.update({m: set(result.get(m, ())) for m in todo})


def source_needs_with_exports(graph: Graph, after: Graph, mod: str, modules: set[str], names: dict,
                              references: set[str] | None, namespaces: dict, uses) -> set[str]:
    """Resolve namespace providers absent from the declaration index lazily.

    An empty exported namespace has no declaration prefix in `.ilean`. Most
    opens already have indexed providers; read exported namespace registrations
    only when an otherwise unaccounted open could depend on a lost module.
    """
    opened = opened_namespaces(graph.text(mod))
    available = namespace_support(after, mod, namespaces, opened)
    unknown = unindexed_namespace_opens(graph.text(mod), namespaces) - available
    if unknown and modules and uses is not None:
        read_namespace_exports(graph, modules, uses)
        if any(namespace_matches(space, ns) for m in modules for space in graph.namespace_exports[m] for ns in unknown):
            survivors = {y for y in after.reads(mod) | after.reads(mod, True) if graph.project(y)}
            read_namespace_exports(graph, survivors, uses)
        namespaces = {m: set(spaces) for m, spaces in namespaces.items()}
        for m, spaces in graph.namespace_exports.items():
            namespaces.setdefault(m, set()).update(spaces)
        available = namespace_support(after, mod, namespaces, opened)
    return source_needs(graph.text(mod), modules, names, references, available, namespaces)


def source_needs(text: str, modules: set[str], names: dict[str, set[str]],
                 references: set[str] | None = None, available_namespaces: set[str] | None = None,
                 module_namespaces: dict[str, set[str]] | None = None) -> set[str]:
    """Prefer resolved elaboration references; retain a conservative fallback.

    An `open VG` doesn't require every module declaring something in VG. It
    needs some surviving provider of that namespace, or a local declaration
    before the open. Only exact namespace matches suppress that guard.
    """
    lines = text.splitlines()
    end = max((n + 1 for n, _ in header_lines(lines)), default=0)
    body = lean_source_evidence.code_only("\n".join(lines[end:]))
    words, opened = source_words(body), opened_namespaces(body)
    available = set(available_namespaces or ())
    first_open = OPEN.search(body)
    prefix = body[:first_open.start()] if first_open else body
    for line in prefix.splitlines():
        s = line.strip()
        if not s or re.fullmatch(r"(?:@\[expose\]\s+)?public\s+(?:meta\s+)?section|section", s):
            continue
        local = re.fullmatch(r"namespace\s+([\w.]+)", s)
        if local:
            parts = local.group(1).split(".")
            available.update(".".join(parts[:i]) for i in range(1, len(parts) + 1))
        break
    opened -= available
    needed = modules & references if references is not None else set()
    for mod in modules:
        declared = names.get(mod, set())
        if references is None and words & {d.rpartition(".")[2] for d in declared}:
            needed.add(mod)
            continue
        spaces = (module_namespaces.get(mod, set()) if module_namespaces is not None and references is not None
                  else {d.rpartition(".")[0] for d in declared})
        if any(s == ns or s.endswith("." + ns) or s.startswith(ns + ".") for ns in opened for s in spaces):
            needed.add(mod)
    return needed


def header_imports(path: pathlib.Path) -> list[str]:
    """The modules a source imports, reading only its header."""
    with open(path, errors="replace") as f:
        return [m.group(4) for _, s in header_lines(f) if (m := IMPORT.fullmatch(s))]


def reverse_index(library: list[str]) -> dict[str, set[str]]:
    users: dict[str, set[str]] = {}
    for j in library:
        for i in header_imports(graph_path(j)):
            users.setdefault(i, set()).add(j)
    return users


def reverse_closure(mod: str, users: dict[str, set[str]]) -> set[str]:
    out, todo = set(), [mod]
    while todo:
        for j in users.get(todo.pop(), ()):
            if j not in out:
                out.add(j)
                todo.append(j)
    return out


# Directories of files reviewed by hand (CLAUDE.md, "Adding a primitive"),
# which `--fix` never edits.
REVIEWED = ("Artifacts", "Generic", "Variants")


def insert_header_command(lines: list[str], command: str, after: int) -> None:
    """Insert outside trailing comments, before documentation or body commands.

    Mark line starts and positions after block-comment terminators in a copy.
    The shared lexer masks marks inside comments. This also handles a comment
    closing on the same line as module documentation or the first declaration.
    Marks are never written to the source.
    """
    marked, positions = [], []
    for line in lines + [""]:
        parts, points, previous, size = ["\0"], [(0, 0)], 0, 1
        for match in re.finditer(r"-/", line):
            part = line[previous:match.end()]
            parts.extend((part, "\0"))
            size += len(part)
            points.append((size, match.end()))
            size += 1
            previous = match.end()
        parts.append(line[previous:])
        marked.append("".join(parts))
        positions.append(points)
    masked = lean_source_evidence.code_only("\n".join(marked)).split("\n")
    for n in range(after, len(marked)):
        for index, column in positions[n]:
            if masked[n][index] != "\0":
                continue
            if column == 0:
                lines.insert(n, command)
            else:
                prefix, suffix = lines[n][:column], lines[n][column:]
                # Keep the following command at its original column; Lean's
                # layout rules can depend on that indentation.
                lines[n:n + 1] = [prefix, command] + ([" " * column + suffix] if suffix.strip() else [])
            return
    raise ValueError("cannot insert an import inside an unterminated header comment")


def render(plan: Plan) -> tuple[dict[pathlib.Path, str], list[str]]:
    """Render all edits before writing any file; preserve comments and deduplicate."""
    if plan.blocked:
        raise ValueError("; ".join(plan.blocked))
    grouped: dict[str, list[Edit]] = {}
    for edit in sorted(set(plan.edits)):
        if reviewed(edit.module):
            raise ValueError(f"refusing to edit reviewed module {edit.module}")
        grouped.setdefault(edit.module, []).append(edit)
    result, done = {}, []
    for mod, edits in grouped.items():
        path = graph_path(mod)
        original = path.read_text()
        if "keep-all" in module_annotations(original):
            raise ValueError(f"{mod}: refusing to change imports of a keep-all module")
        lines = original.split("\n")
        # Demote/remove before adding: additions may upgrade plain imports.
        edits.sort(key=lambda e: (e.action.startswith("add"), e))
        for edit in edits:
            x, op = edit.dependency, edit.action
            is_meta = op.endswith("_meta")
            make_public = op.startswith("add_public")
            before = list(lines)
            commands = list(header_lines(lines))
            imports = [(n, IMPORT.fullmatch(s)) for n, s in commands if IMPORT.fullmatch(s)]
            matching = [(n, m) for n, m in imports if m.group(4) == x
                        and bool(m.group(2)) == is_meta and not m.group(3)]
            if op in NARROWING:
                first_private = min((n for n, m in matching if not m.group(1)), default=None)
                public_target = op in ("demote", "remove_public")
                matching = [(n, m) for n, m in matching if bool(m.group(1)) == public_target]
                if not matching:
                    expected = "public" if public_target else "private"
                    raise ValueError(f"{mod}: {expected} import {x} no longer present; analyze again")
                if any("shake: keep" in lines[n] for n, _ in matching):
                    raise ValueError(f"{mod}: refusing to change protected import {x}")
                # Keep the first occurrence in place: dropping an earlier
                # public copy in favour of a later private copy changes load
                # order, which can change instance selection.
                keep_line = (matching[0][0] if op == "demote" and
                             (first_private is None or matching[0][0] < first_private) else None)
                for n, m in reversed(matching):
                    if n == keep_line:
                        lines[n] = re.sub(r"^(\s*)public\s+", r"\1", lines[n], count=1)
                        if lines[n] == before[n]:
                            raise ValueError(f"{mod}: cannot safely edit this import layout: {x}")
                    else:
                        # Remove only the command, retaining attached comments
                        # (including a block comment spanning following lines).
                        pattern = (r"^(\s*)" + (r"public\s+" if m.group(1) else "")
                                   + (r"meta\s+" if is_meta else "") + r"import\s+" + re.escape(x) + r"(?=\s|--|/-|$)")
                        remaining, count = re.subn(pattern, r"\1", lines[n], count=1)
                        if not count:
                            raise ValueError(f"{mod}: cannot safely edit this import layout: {x}")
                        if remaining.strip():
                            lines[n] = remaining
                        else:
                            del lines[n]
            elif op in ("add", "add_public", "add_meta", "add_public_meta"):
                public_present = any(m.group(1) for _, m in matching)
                promotable = [(n, m) for n, m in matching if "shake: keep" not in lines[n]]
                if make_public and not public_present and promotable:
                    n, _ = promotable[0]
                    lines[n] = re.sub(r"^(\s*)(?=(?:meta\s+)?import\b)", r"\1public ", lines[n], count=1)
                    if lines[n] == before[n]:
                        raise ValueError(f"{mod}: cannot safely promote this import layout: {x}")
                elif not matching or (make_public and not public_present):
                    at = imports[-1][0] + 1 if imports else commands[-1][0] + 1
                    insert_header_command(lines, ("public " if make_public else "")
                                          + ("meta " if is_meta else "") + f"import {x}", at)
            else:
                raise ValueError(f"unknown import operation: {op}")
            if lines != before:
                done.append(f"{path.relative_to(ROOT)}: {op} {x}")
        text = "\n".join(lines)
        if text != original:
            result[path] = text
    return result, done


def fix(plan: Plan) -> list[str]:
    """Apply executable operations, never parse diagnostics as instructions."""
    rendered, done = render(plan)
    for path, text in rendered.items():
        path.write_text(text)
    return done


BUILD_LOG = LEAN / ".lake" / "check-imports-build.log"


def build_failures(mods: list[str], *, timeout: float | None = None, phase: str = "verify",
                   log: pathlib.Path | None = None, attempts: list | None = None) -> set[str]:
    """Distinguish Lean failures from unknown failures, interruption and timeout."""
    path = log or BUILD_LOG
    progress(f"{phase} build log: {path}")
    attempt = lean_import_build.Attempt(phase=phase, targets=mods, log=str(path))
    try:
        lean_import_build.build(mods, LEAN, path, phase, timeout, attempt)
    finally:
        if attempts is not None:
            attempts.append(attempt.json())
        if path != BUILD_LOG and path.is_file():
            BUILD_LOG.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, BUILD_LOG)
    if attempt.timed_out:
        raise TimeoutError(f"{phase} build exceeded {timeout}s; Lean processes stopped; see {path}")
    if attempt.succeeded:
        return set()
    if not attempt.failures:
        raise RuntimeError(f"Lake exited {attempt.returncode} without identifiable failed modules; see {path}")
    return set(attempt.failures)


@lean_import_build.interruptible
def fix_and_verify(plan: Plan, library: list[str], *, timeout: float | None = None,
                   max_attempts: int = 3, audit: dict | None = None,
                   verify_batch: int = 32) -> tuple[list[str], list[str]]:
    """Warm and check the baseline, then verify a bounded import-edit transaction.

    Every attempt has a durable log. Returning kept edits requires a successful
    verification build. Unknown failures or cancellation restore the whole batch.
    """
    if not plan.edits:
        return [], []
    if max_attempts < 1 or verify_batch < 1:
        raise ValueError("verification attempts and batch size must be positive")
    saved = {}
    record = audit if audit is not None else {}
    run = LEAN / ".lake/import-verification" / str(time.time_ns())
    manifest = run / "result.json"
    record.update({"build_verified": False, "status": "pending", "manifest": str(manifest),
                   "proposed_edits": [asdict(e) for e in plan.edits], "attempts": [],
                   "kept": [], "undone": [], "verify_batch": verify_batch})

    def build_scope(phase, stem):
        for k in range(0, len(targets), verify_batch):
            part = targets[k:k + verify_batch]
            suffix = f"-chunk-{k // verify_batch + 1}" if len(targets) > verify_batch else ""
            failing = build_failures(part, timeout=timeout, phase=phase, log=run / f"{stem}{suffix}.log",
                                     attempts=record["attempts"])
            lean_import_build.save(manifest, record)
            if failing:
                return failing
        return set()

    undone, applied = [], False
    try:
        render(plan)  # validate every operation before spending time on a baseline
        saved = {path: path.read_text() for path in plan.paths()}
        users = reverse_index(library)
        modules = {e.module for e in plan.edits}
        targets = sorted(modules | set().union(*(reverse_closure(m, users) for m in modules)))
        record["targets"] = targets
        lean_import_build.save(manifest, record)
        progress(f"checking baseline of {len(targets)} modules before editing")
        baseline = build_scope("baseline", "baseline")
        if baseline:
            raise RuntimeError("baseline does not build; no import edits applied: " + ", ".join(sorted(baseline)))
        if any(path.read_text() != original for path, original in saved.items()):
            raise RuntimeError("sources changed during the baseline build; analyze again")
        applied = True
        done = fix(plan)
        edited = {".".join(p.relative_to(LEAN).with_suffix("").parts): p
                  for p in saved if p.read_text() != saved[p]}
        attempt_number = 0
        while edited:
            if attempt_number >= max_attempts:
                raise RuntimeError(f"verification attempt budget ({max_attempts}) exhausted; restoring the batch")
            attempt_number += 1
            progress(f"verification {attempt_number}/{max_attempts}: {len(targets)} targets ({len(edited)} edited)")
            failing = build_scope("verify", f"verify-{attempt_number}")
            if not failing:
                kept = [d for d in done if any(d.startswith(str(p.relative_to(ROOT)) + ":") for p in edited.values())]
                record.update({"build_verified": True, "status": "verified", "kept": kept, "undone": sorted(undone)})
                return kept, sorted(undone)
            progress(f"{len(failing)} modules fail; undoing the nearest edits")
            culprits = set(edited) & failing
            if not culprits:
                direct = set().union(*(set(header_imports(graph_path(f))) for f in failing
                                       if graph_path(f).is_file()))
                culprits = set(edited) & direct
            if not culprits:
                culprits = {m for m in edited if reverse_closure(m, users) & failing}
            if not culprits:
                raise RuntimeError("build failures could not be attributed to edits; restoring the batch")
            for m in sorted(culprits):
                path = edited.pop(m)
                path.write_text(saved[path])
                undone.append(m)
        record.update({"status": "rejected", "undone": sorted(undone)})
        return [], sorted(undone)
    except BaseException as error:
        if applied:
            for path, text in saved.items():
                path.write_text(text)
            record["undone"] = sorted(".".join(p.relative_to(LEAN).with_suffix("").parts) for p in saved)
        record.update({"status": "aborted", "error": f"{type(error).__name__}: {error}", "kept": []})
        raise
    finally:
        lean_import_build.save(manifest, record)


def library_modules(names) -> list[str]:
    out = []
    for m in names:
        p = LEAN / pathlib.Path(*m.split(".")).with_suffix(".lean")
        if m.split(".")[0] == LIBRARY and p.is_file() and is_module(p.read_text()):
            out.append(m)
    return sorted(out)


def dependency_roots() -> list[pathlib.Path]:
    """Where Lake finds the sources of the project and its dependencies."""
    prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=LEAN, capture_output=True,
                            text=True, check=True).stdout.strip()
    packages = sorted(p for p in (LEAN / ".lake/packages").iterdir() if p.is_dir())
    return [LEAN, pathlib.Path(prefix) / "src/lean", *packages]


@lean_import_build.interruptible
def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("plan", nargs="?", type=pathlib.Path)
    parser.add_argument("-m", "--modules", nargs="+", default=[])
    parser.add_argument("--base", help="check only the imports added since this git revision")
    parser.add_argument("--fix", action="store_true",
                        help="apply findings and verify the affected library modules")
    parser.add_argument("--dependencies", nargs="+", default=[], metavar="PREFIX",
                        help="also remove the unused imports of these dependencies' modules (e.g. Mathlib)")
    parser.add_argument("--batch", type=int, default=1000, help="maximum modules per shake/build call")
    parser.add_argument("--read-batch", type=int, default=32, help="maximum roots per declaration reader")
    parser.add_argument("--read-timeout", type=float, default=120, help="seconds per declaration-reader process")
    parser.add_argument("--build-timeout", type=float, help="seconds per build/shake invocation")
    args = parser.parse_args(argv)
    if (args.batch < 1 or args.read_batch < 1 or args.read_timeout <= 0
            or (args.build_timeout is not None and args.build_timeout <= 0)):
        parser.error("batch sizes and timeouts must be positive")
    names = list(args.modules)
    if args.plan:
        plan = json.loads(args.plan.read_text())
        if "edited" not in plan:
            print("The plan has no edited modules (no manifest of a last build): nothing to check.")
            return 0
        names += plan["edited"]
    mods = library_modules(names)
    if len(mods) > MAX_MODULES:
        print(f"{len(mods)} modules edited, more than {MAX_MODULES}: not checked.")
        return 0
    if not mods:
        print("Public imports OK (no module edited)")
        return 0
    new = {m: new_public(m, args.base) for m in mods}
    plain = {m: new_plain(m, args.base) for m in mods}
    meta_plain = {m: new_meta(m, args.base) for m in mods}
    mods = [m for m in mods if any(selected[m] is None or selected[m] for selected in (new, plain, meta_plain))]
    if not mods:
        print("Public imports OK (no import added)")
        return 0
    library = library_modules(
        ".".join(f.relative_to(LEAN).with_suffix("").parts) for f in (LEAN / LIBRARY).rglob("*.lean"))
    # Share freshness checks, persistent raw evidence and bounded readers with
    # the bulk planner. In particular, downstream cache hits must still build
    # their roots before their declarations can be trusted.
    import trim_lean_imports as bulk
    state = bulk.State(LEAN / ".lake/trim-imports.json")
    shaken = bulk.shaken(mods, state, args.batch, timeout=args.build_timeout)
    evidence = bulk.replay.Evidence(bulk.cached_uses(state, args.build_timeout, args.read_timeout),
                                    min(args.batch, args.read_batch))
    plan = analyze(mods, shaken, Graph(dependency_roots(), args.dependencies), new, plain, evidence, library,
                   meta_plain=meta_plain)
    state.save()
    found = plan.messages
    for p in found:
        print(p, file=sys.stderr)
    for message in plan.blocked:
        print("blocked:", message, file=sys.stderr)
    if plan.deferred:
        print(f"deferred: {len(plan.deferred)} public boundaries retained by policy", file=sys.stderr)
    if not found:
        print(f"Imports OK ({len(mods)} modules)")
        return 0
    if args.fix and not plan.blocked:
        kept, undone = fix_and_verify(plan, library, timeout=args.build_timeout)
        for d in kept:
            print("fixed:", d)
        for m in undone:
            print(f"undone (did not build with the change): {m}")
        print(f"{len(kept)} changes kept after verification; {len(undone)} files' changes undone. "
              "Run the check again to see what is left.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
