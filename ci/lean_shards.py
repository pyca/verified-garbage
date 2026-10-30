#!/usr/bin/env python3
"""Plans how CI splits the Lean build across runners.

CI restores the last build `main` saved, and Lake rebuilds only the modules
whose sources changed since, and the modules that read their outputs: those
importing them, and those importing a module that passes them on (`public
import`, `reads`). A module that imports a changed module privately is
rebuilt, but its own outputs come out as they were, so Lake rebuilds nothing
beyond it on its account; the plan counts it among the modules to rebuild
but not what imports it. Native library consumers also depend on the shared
libraries in their compile traces, except for libraries opting out with
`platformIndependent = true` (the ordinary proofs and tests). The build is
limited mostly by throughput, so the modules to rebuild are split into
shards that build in parallel on separate runners, as many as the work
needs: none when one would do (the `lean` job builds it), or when shards
would save less than their own overhead, up to `MAX_SHARDS` when everything
changed, but no more than make the build faster.

`main` saves a manifest next to its build: the hash of every module's source,
of the build's inputs, and how long each module took to build (from the shards' build logs, kept
from earlier builds for the modules this one did not rebuild). A plan
compares the sources with the manifest's to find the modules to rebuild,
estimates each from its time, and packs them into shards: a shard builds the
stale modules that no other stale module imports, directly or transitively,
and everything they import. Unchanged downstream modules need not bind
otherwise independent rebuilds to the same shard. The targets are packed
by the time to rebuild their imports, largest first, each into the shard
where the estimate it leaves, plus the work it adds there (as time on a
runner, weighed by each of `REUSE_WEIGHTS` in turn), is the least:
a shard with a long chain takes other work only until it would finish after
the chain, and a sink goes where much of what it imports is built already,
rather than building it again elsewhere, unless that shard is the slower by
more than the work it saves. A change to the inputs (the toolchain, the
dependencies or the lakefile's settings) rebuilds every module, but not one
that only adds a module to a library or removes one (the lakefile's `globs`
and `roots`): that rebuilds just the modules it moves (and, through their
imports, what imports them). Each module's outputs belong to one shard (the
first that builds it), so the shards' outputs together are the whole build. A plan
is only an estimate: whatever the shards leave unbuilt, the job that
assembles their outputs (the last shard to finish, normally) builds.

For each useful count up to MAX_SHARDS (one whose shards could finish
within SLACK of the fastest plan if they shared the work evenly) and each
reuse weight, a dependency-constrained simulation estimates the packing's
build time, including serial phases that cannot
overlap the parallel work. Compare those times plus SHARD_OVERHEAD with a
single runner's time; among plans within SLACK of the fastest, choose the
least total module work (counting duplicated imports), then fewer runners.
Finally, a bounded search moves targets to reuse shared imports without
exceeding the same finish-time budget.

  lean_shards.py plan MANIFEST PLAN     write the plan for the sources (with
                                        the manifest's build, which may be
                                        missing) to PLAN, and print the number
                                        of shards (`count=`) and their names
                                        (`shards=`, a JSON list) for
                                        $GITHUB_OUTPUT
  lean_shards.py targets PLAN SHARD     the sinks of SHARD, as `lake build`
                                        targets (`+Module`), one per line
  lean_shards.py closure PLAN SHARD     the modules SHARD's build needs (its
                                        sinks, what they import, and the
                                        precompiled libraries of those), one
                                        per line: what it needs of the last
                                        build
  lean_shards.py outputs PLAN SHARD     of the paths on stdin (files under
                                        `lean/.lake/build/`, relative to it),
                                        those that are outputs of SHARD's
                                        modules
  lean_shards.py times [--observations]  the time of each module a `lake build`
                                        log on stdin built, as JSON; with
                                        --observations, keep native components
                                        separate for manifest updates
  lean_shards.py manifest OLD TIMES...  the manifest of the sources, with the
                                        times of TIMES (files of `times`) and,
                                        for the modules they lack, of OLD
                                        (which may be missing)
  lean_shards.py prune BUILD            delete the outputs under BUILD
                                        (`lean/.lake/build`) of the project's
                                        modules whose sources are gone, which
                                        Lake never deletes, so that the saved
                                        build does not keep them forever
"""

import hashlib
import functools
import heapq
import json
import math
import multiprocessing
import os
import pathlib
import re
import statistics
import sys
import time
import tomllib

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"
# The libraries of `lean/lakefile.toml`: `VerifiedGarbage.+` and
# `VerifiedGarbageTest.+` (every module under each); `True` reads a root
# module as well, `lean/<library>.lean`, if there is one (there is none).
LIBRARIES = {"VerifiedGarbage": True, "VerifiedGarbageTest": False}
# Files any change of which rebuilds every module (the lakefile's but for
# which modules each library has: see `lakefile_inputs`).
INPUTS = ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]
# The keys of a library in the lakefile that list its modules.
MODULE_LISTS = ("globs", "roots")
# More shards wait for runners, and build what they share again: in CI's
# metrics, full rebuilds (about 43000 s of work) took 1360-1700 s on 16
# shards, building 40% of the work twice, and about 1320 s on 12.
MAX_SHARDS = 12
# What a run with shards takes beyond its slowest shard's build, more than
# the `lean` job takes beyond building everything itself: the shards wait
# for runners, and upload and download their outputs (in CI's metrics, 262 s
# beyond the slowest build, against 172 s beyond the build in the `lean`
# job). Shards are taken only when they save more than this.
SHARD_OVERHEAD = 90.0
# How much slower than the fastest finish (including overhead) a cheaper
# plan may be. The single-runner build participates in the same comparison.
SLACK = 0.05
# How many modules a runner's build runs at once (as measured: the shards'
# module times add up to 5.4 times their builds' wall times). The simulation
# has ceil(PARALLELISM) slots sharing this throughput when all are occupied.
PARALLELISM = 5.4
# How heavily packing weighs the work a sink adds to a shard (modules the
# shard does not build yet), against the shard's estimated time: 1 is that
# work as time on a runner, more makes a sink rather join the shards that
# build its imports already. Which weight packs best depends on the
# rebuild (in a full rebuild of CI's, 8 halved the work built twice and
# finished 9% sooner, but 12 left one shard much slower): the plan tries
# each and keeps the fastest by the simulation.
REUSE_WEIGHTS = (1.0, 2.0, 4.0, 6.0, 8.0)
# The time to check that a module is up to date, and to build one the
# manifest has no time for when it has none at all.
UP_TO_DATE = 0.02
DEFAULT_TIME = 3.0
# `import`, and in a module `public`, `meta` and `all` imports.
# Leading whitespace stays on one line; inter-keyword whitespace still
# permits multiline imports, without rescanning runs of blank lines.
IMPORT_KIND = re.compile(r"^[^\S\r\n]*(public\s+)?(?:meta\s+)?import\s+(all\s+)?(\S+)", re.M)
BUILT = re.compile(r"\bBuilt (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")
# The steps of a module of a precompiled library after its `.olean`.
NATIVE_FACETS = ("c.o", "dynlib")


def modules() -> dict[str, pathlib.Path]:
    mods = {}
    depth = len(LEAN.parts)
    for lib, root in LIBRARIES.items():
        if root and (LEAN / f"{lib}.lean").is_file():
            mods[lib] = LEAN / f"{lib}.lean"
        for f in (LEAN / lib).rglob("*.lean"):
            # rglob supplies paths below LEAN; slicing their components
            # avoids pathlib's repeated ancestor checks for every file.
            mods[".".join(f.parts[depth:])[:-5]] = f
    return dict(sorted(mods.items()))


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lakefile_inputs(text: str) -> tuple[str, dict[str, list[str]]]:
    """The hash of the lakefile but for its libraries' module lists, and
    each library's entries of those lists (`globs:X`, `roots:X`)."""
    config = tomllib.loads(text)
    libraries = {}
    for lib in config.get("lean_lib", []):
        libraries[lib["name"]] = sorted(f"{k}:{e}" for k in MODULE_LISTS for e in lib.get(k, []))
        for k in MODULE_LISTS:
            lib.pop(k, None)
    settings = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    return settings, libraries


def inputs() -> dict:
    """What the manifest records of the build's inputs."""
    settings, libraries = lakefile_inputs((LEAN / "lakefile.toml").read_text())
    files = {f: digest(LEAN / f) for f in INPUTS if f != "lakefile.toml"}
    return {**files, "lakefile.toml settings": settings, "libraries": libraries}


def precompiled_libraries(closure):
    """The project's native libraries, in Lake's configuration order."""
    config = tomllib.loads((LEAN / "lakefile.toml").read_text())
    return {
        lib["name"]: frozenset(library_members(lib, closure))
        for lib in config.get("lean_lib", []) if lib.get("precompileModules")
    }


def library_members(lib: dict, closure: dict[str, frozenset[str]]) -> set[str]:
    """The modules (of `closure`) a library's module lists take, as
    `matches` says: an exact name or a root is looked up rather than matched
    against every module, which only a glob of a prefix needs."""
    out = set()
    for k in MODULE_LISTS:
        for e in lib.get(k, []):
            if k == "roots" or not e.endswith((".*", ".+")):
                named = closure.get(e, {e}) if k == "roots" else {e}
                out.update(m for m in named if m in closure and matches(f"{k}:{e}", m, closure))
            else:
                out.update(m for m in closure if matches(f"{k}:{e}", m, closure))
    return out


def build_requirements(closure, libraries):
    """Add whole native libraries exactly as the selective cache restore does.

    Importing one native module can link its whole library, including modules
    outside the ordinary import closure. Scheduling and restoration must agree
    on those dependencies. Expand library groups once, rather than walking
    their imports again for every sink and candidate shard count.
    """
    expanded = {name: set().union(*(closure[m] for m in members))
                for name, members in libraries.items()}
    changed = True
    while changed:
        changed = False
        for name, part in expanded.items():
            for other, members in libraries.items():
                if part & members and not expanded[other] <= part:
                    part.update(expanded[other])
                    changed = True
    return {m: part.union(*(expanded[name] for name, members in libraries.items() if part & members))
            for m, part in closure.items()}


def needed(targets: list[str], closure: dict[str, frozenset[str]]) -> set[str]:
    """The ordinary and native-library imports a shard must restore."""
    required = build_requirements(closure, precompiled_libraries(closure))
    return set().union(*(required[t] for t in targets))


def matches(entry: str, module: str, closure: dict[str, frozenset[str]]) -> bool:
    """Whether a library's module list entry (`globs:X` or `roots:X`) takes
    `module`: Lake's `X.*` is X and the modules under it, `X.+` those under
    it, and a root is a module with everything it imports."""
    kind, _, pattern = entry.partition(":")
    if kind == "roots":
        return module in closure.get(pattern, {pattern})
    if pattern.endswith(".*"):
        return module == pattern[:-2] or module.startswith(pattern[:-1])
    if pattern.endswith(".+"):
        return module.startswith(pattern[:-1])
    return module == pattern


def imported_by(text: str, mods) -> list[str]:
    """The modules of the project (of `mods`) the source `text` imports."""
    return [i for _, _, i in import_kinds(text, mods)]


def import_kinds(text: str, mods, modes=None) -> list[tuple[bool, bool, str]]:
    """Project imports, with their public/all visibility, in source order."""
    # Every match starts on a line containing one of these keywords.
    # Literal searches skip proof bodies much faster than trying an
    # anchored regex at every line. Keep regex validation and nonoverlap
    # semantics, including public/meta imports split across multiple lines.
    starts = set()
    for word in ("import", "public", "meta"):
        pos = text.find(word)
        while pos >= 0:
            starts.add(text.rfind("\n", 0, pos) + 1)
            # One candidate per line suffices, even in long generated
            # strings containing the keyword many times.
            newline = text.find("\n", pos)
            if newline < 0:
                break
            pos = text.find(word, newline + 1)
    kinds = []
    end = 0
    for start in sorted(starts):
        if start < end:
            continue
        match = IMPORT_KIND.match(text, start)
        if match:
            end = match.end()
            p, a, i = match.groups()
            if i in mods:
                kinds.append((bool(p), bool(a), i))
                if modes is not None and "meta" in match.group(0).split()[:-1]:
                    modes.setdefault("meta", []).append(i)
                    if p:
                        modes.setdefault("public_meta", []).append(i)
    return kinds


def imports(mods: dict[str, pathlib.Path]) -> dict[str, list[str]]:
    """The modules of the project each module imports."""
    return {m: imported_by(f.read_text(), mods) for m, f in mods.items()}


def is_module(text: str) -> bool:
    """Whether the source `text` starts with `module`, after any comments."""
    comment = False
    pos = 0
    while pos < len(text):
        end = text.find("\n", pos)
        if end < 0:
            end = len(text)
        s = text[pos:end].strip()
        pos = end + 1
        if comment:
            comment = not s.endswith("-/")
        elif s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
        elif s == "module":
            return True
        elif s and not s.startswith("--"):
            return False
    return False


def visibility(text: str, mods) -> tuple[list[str], list[str]] | None:
    """Of the modules of the project (of `mods`) the source `text` imports,
    those it passes on to its importers (`public` imports: Lake's trace of a
    module importing it has their outputs too) and those it imports `all`;
    None for a file that is not a module, which Lake builds with the whole
    closure of its imports, every module's outputs, private parts included."""
    if not is_module(text):
        return None
    kinds = import_kinds(text, mods)
    return [i for p, _, i in kinds if p], [i for _, a, i in kinds if a]


def visibilities(mods: dict[str, pathlib.Path]) -> dict[str, tuple[list[str], list[str]] | None]:
    """`visibility` of each module of the project."""
    return {m: visibility(f.read_text(), mods) for m, f in mods.items()}


def source_info(mods, source_bytes=None, import_modes=None):
    """Read/hash each source once and share one import scan between graphs.

    Hash the original bytes, but normalize newlines for parsing just as
    Path.read_text does. Sources, imports, and visibility describe the same
    read of each file, including for the final `edited` list.
    """
    imps, vis, hashes = {}, {}, {}
    for m, path in mods.items():
        data = path.read_bytes()
        hashes[m] = hashlib.sha256(data).hexdigest()
        if source_bytes is not None:
            source_bytes[m] = len(data)
        text = data.decode("utf-8")
        if "\r" in text:
            text = text.replace("\r\n", "\n").replace("\r", "\n")
        imps[m], vis[m], modes = parse_imports(text, mods)
        if import_modes is not None and modes:
            import_modes[m] = modes
    return imps, vis, hashes


def parse_imports(text: str, mods):
    """A source's imports of modules of the project (of `mods`), its
    `visibility` and its import modes (`meta`, `public_meta`), from one scan."""
    modes = {}
    kinds = import_kinds(text, mods, modes)
    vis = ([i for p, _, i in kinds if p], [i for _, a, i in kinds if a]) if is_module(text) else None
    return [i for _, _, i in kinds], vis, modes


def reads(
    imps: dict[str, list[str]],
    closure: dict[str, frozenset[str]],
    vis: dict[str, tuple[list[str], list[str]] | None],
    modes: dict | None = None,
    among: frozenset[str] | None = None,
) -> dict[str, frozenset[str]]:
    """The modules of the project whose outputs each module's build reads
    (its trace), as Lake reads them: each module it imports, and what those
    pass on (`public import`), transitively; with an `import all`, also what
    that module imports; with the whole closure for a file that is not a
    module. `meta import` also reads interpreter IR through private imports;
    a public meta import passes that dependency on. For ordinary imports,
    changes behind a private import can leave the importer's public outputs
    unchanged, allowing its downstream ordinary importers to stay cached.

    With `among` (and `closure` from `closures(imps, among)`), each trace
    is intersected with it: enough to ask which modules read any of a few,
    without building every module's whole trace."""
    own = (lambda m: frozenset({m})) if among is None else (lambda m: frozenset({m}) & among)
    # Meta traces include interpreter IR of private transitive imports too.
    # Public meta imports pass that dependency on to ordinary importers.
    meta = {m: set(k.get("meta", [])) for m, k in (modes or {}).items()}
    public_meta = {m: set(k.get("public_meta", [])) for m, k in (modes or {}).items()}
    passed: dict[str, frozenset[str]] = {}
    for root in imps:
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if m in passed:
                continue
            on = imps[m] if vis.get(m) is None else vis[m][0]
            if ready:
                passed[m] = own(m).union(*(closure[i] if i in public_meta.get(m, ()) else passed[i] for i in on))
            else:
                stack.append((m, True))
                stack += [(i, False) for i in on if i not in passed]
    @functools.cache
    def all_trace(m):
        if vis.get(m) is None:
            return closure[m]
        return own(m).union(*(
            all_trace(i) if i in vis[m][1] else closure[i] if i in meta.get(m, ()) else passed[i]
            for i in imps[m]))

    out = {}
    for m in imps:
        if vis.get(m) is None:
            out[m] = closure[m] - {m}
        else:
            out[m] = frozenset().union(*(
                all_trace(i) if i in vis[m][1] else closure[i] if i in meta.get(m, ()) else passed[i]
                for i in imps[m]))
    return out


def native_trace_modules(closure):
    """Modules whose effective library does not opt out of native hashes.

    Lake resolves a module through the last matching library. Ordinary proofs
    in this project deliberately use platformIndependent=true; native libraries
    do not. Do not invalidate those ordinary proofs for unrelated native work.
    """
    config = tomllib.loads((LEAN / "lakefile.toml").read_text())
    dependent = set(closure)
    for lib in config.get("lean_lib", []):
        members = library_members(lib, closure)
        if lib.get("platformIndependent") is True:
            dependent.difference_update(members)
        else:
            dependent.update(members)
    return dependent


def native_reads(imps, closure, libraries, trace_modules=None):
    """Source dependencies of the native libraries in Lake's compile trace.

    Even a private/transitive import loads native plugins. Across libraries,
    Lake hashes the whole shared library, so an otherwise unrelated member
    can invalidate an importer. Inside one native library it loads only the
    imported modules' dynlibs, not unrelated siblings. Keep this separate from
    public/private Lean interface propagation.
    """
    owners = {m: name for name, members in libraries.items() for m in members}
    groups = {name: set().union(*(closure[m] for m in members))
              for name, members in libraries.items()}
    # Shared libraries also link native libraries reached by their members.
    changed = True
    while changed:
        changed = False
        for name, part in groups.items():
            for other, members in libraries.items():
                if other != name and part & members and not groups[other] <= part:
                    part.update(groups[other])
                    changed = True
    out = {}
    for m, imports in closure.items():
        if trace_modules is not None and m not in trace_modules:
            out[m] = frozenset()
            continue
        dependencies = set()
        for name, members in libraries.items():
            imported = (imports - {m}) & members
            if not imported:
                continue
            if owners.get(m) == name:
                dependencies.update(set().union(*(closure[i] for i in imported)))
            else:
                dependencies.update(groups[name])
        out[m] = frozenset(dependencies - {m})
    return out


def stale_of(changed: set[str], read: dict[str, frozenset[str]]) -> set[str]:
    """The modules a build rebuilds when the modules `changed` change: those,
    and every module that reads one of them (`reads`)."""
    return set(changed) | {m for m, r in read.items() if r & changed}


def closures(imps: dict[str, list[str]], among: frozenset[str] | None = None) -> dict[str, frozenset[str]]:
    """Each module and everything it imports, directly or not; with `among`,
    only those of these."""
    own = (lambda m: frozenset({m})) if among is None else (lambda m: frozenset({m}) & among)
    done: dict[str, frozenset[str]] = {}
    for root in imps:
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if m in done:
                continue
            if ready:
                done[m] = own(m).union(*(done[i] for i in imps[m]))
            else:
                stack.append((m, True))
                stack += [(i, False) for i in imps[m] if i not in done]
    return done


def paths(imps: dict[str, list[str]], cost: dict[str, float]) -> dict[str, float]:
    """For each module of `cost`, the time of the longest chain of imports
    ending in it through modules of `cost` (those a build builds), each
    taking its time there: the least time a build takes to get to it,
    however many modules it builds at once."""
    done: dict[str, float] = {}
    for root in cost:
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if m in done:
                continue
            within = [i for i in imps[m] if i in cost]
            if ready:
                done[m] = cost[m] + max((done[i] for i in within), default=0.0)
            else:
                stack.append((m, True))
                stack += [(i, False) for i in within if i not in done]
    return done


def estimate(work: float, path: float) -> float:
    """The time a runner takes to build modules taking `work` in all, whose
    longest chain of imports (critical path) takes `path`."""
    return max(work / PARALLELISM, path)


def wall_time(imps: dict[str, list[str]], cost: dict[str, float]) -> float:
    """The estimated time of a build of the modules of `cost`, each taking
    its time there."""
    return build_time(imps, cost)


def build_time(imps: dict[str, list[str]], cost: dict[str, float]) -> float:
    """List-schedule a build, imports first, prioritizing the longest
    remaining chain. At most ceil(PARALLELISM) modules run concurrently;
    when all slots are busy they share PARALLELISM modules' throughput.

    Unlike max(work / parallelism, critical path), this accounts for a
    narrow dependency chain before or after the parallel part of a build.
    Module durations and effective throughput are empirical estimates,
    not a model of Lake's exact scheduling or the runner's CPU threads.
    """
    return _BuildGraph(imps, cost).time()


class _BuildGraph:
    """Reuse integer-indexed dependencies across candidate simulations.

    `time` accepts import-closed subsets of this graph. A standalone
    `build_time` constructs its graph from exactly the supplied costs,
    so dependencies without supplied costs are excluded as before.
    """

    def __init__(self, imps, cost):
        names = sorted(cost)
        self.index = {m: i for i, m in enumerate(names)}
        self.cost = [cost[m] for m in names]
        self.users = [[] for _ in names]
        self.pending = [0] * len(names)
        for m, n in self.index.items():
            for dep in imps[m]:
                i = self.index.get(dep)
                if i is not None:
                    self.users[i].append(n)
                    self.pending[n] += 1
        self.order = [i for i, n in enumerate(self.pending) if not n]
        left = self.pending.copy()
        for i in self.order:
            for u in self.users[i]:
                left[u] -= 1
                if not left[u]:
                    self.order.append(u)
        if len(self.order) != len(names):
            raise ValueError("cycle in Lean imports")
        self.cache = {}

    def time(self, modules=None):
        key = None if modules is None else (PARALLELISM, frozenset(modules))
        if key is not None:
            cached = self.cache.get(key)
            if cached is not None:
                return cached
        size = len(self.cost)
        selected = bytearray(size)
        if modules is None:
            selected[:] = b"\x01" * size
            order = self.order
        else:
            if not modules:
                return 0.0
            for m in modules:
                selected[self.index[m]] = 1
            order = [i for i in self.order if selected[i]]
        users, cost = self.users, self.cost
        tail = [0.0] * size
        for i in reversed(order):
            longest = 0.0
            for u in users[i]:
                if selected[u] and tail[u] > longest:
                    longest = tail[u]
            tail[i] = cost[i] + longest
        pending = self.pending.copy()
        ready = [(-tail[i], i) for i in order if not pending[i]]
        heapq.heapify(ready)
        running = []
        service = elapsed = 0.0
        slots = math.ceil(PARALLELISM)
        while ready or running:
            while ready and len(running) < slots:
                _, i = heapq.heappop(ready)
                heapq.heappush(running, (service + cost[i], i))
            finish = running[0][0]
            elapsed += (finish - service) * max(1.0, len(running) / PARALLELISM)
            service = finish
            while running and running[0][0] <= service:
                _, i = heapq.heappop(running)
                for u in users[i]:
                    if selected[u]:
                        pending[u] -= 1
                        if not pending[u]:
                            heapq.heappush(ready, (-tail[u], u))
        if key is not None:
            self.cache[key] = elapsed
        return elapsed


def rebuild_targets(stale: set[str], closure: dict[str, frozenset[str]]) -> list[str]:
    """The maximal stale modules under the *full* import relation.

    Private imports limit invalidation, not what a build needs. Targeting
    these modules covers every stale module without bundling independent
    rebuilds together through an unchanged downstream importer.
    """
    covered = set()
    for m in sorted(stale):
        covered.update((closure[m] & stale) - {m})
    return sorted(stale - covered)


def read_json(path: str) -> dict:
    p = pathlib.Path(path)
    return json.loads(p.read_text()) if p.is_file() else {}


class _Sinks:
    """What packing reads of each sink, the same for every count and weight.

    A build restores the modules it does not rebuild, at `UP_TO_DATE` each:
    packing weighs each sink's rebuilt modules (`rebuilt`) one by one, and
    counts its restored ones (`restored`, a bit mask), which takes a
    fraction of the time of subtracting its whole closure from each shard.
    """

    def __init__(self, sinks, closure, cost):
        self.rebuilt = {s: frozenset(m for m in closure[s] if cost[m] != UP_TO_DATE) for s in sinks}
        kept = {s: closure[s] - self.rebuilt[s] for s in sinks}
        index = {m: i for i, m in enumerate(sorted(set().union(*kept.values())))}
        self.restored = {}
        for s in sinks:
            bits = bytearray((len(index) + 7) // 8)
            for m in kept[s]:
                i = index[m]
                bits[i >> 3] |= 1 << (i & 7)
            self.restored[s] = int.from_bytes(bits, "little")


# What `_Packings`' worker processes pack: set before they start, which
# they inherit (forked) rather than receive.
_PACKING = None


def _pack_one(task):
    n, reuse = task
    sinks, closure, cost, path, prepared = _PACKING
    return pack(n, sinks, closure, cost, path, reuse, prepared)


class _Packings:
    """Each count's packings, one per reuse weight. With many sinks (a
    packing then takes a large part of a second) and CPUs to spare, worker
    processes pack them at once, forked when first needed; the packings are
    the same as one after another."""

    # Fewer sinks pack in less time than forking takes.
    PARALLEL_SINKS = 200

    def __init__(self, sinks, closure, cost, path, prepared):
        global _PACKING
        _PACKING = (sinks, closure, cost, path, prepared)
        self.pool = None
        cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count() or 1
        self.workers = min(len(REUSE_WEIGHTS), cpus)
        if (len(sinks) < self.PARALLEL_SINKS
                or "fork" not in multiprocessing.get_all_start_methods()):
            self.workers = 1

    def __call__(self, n):
        tasks = [(n, reuse) for reuse in REUSE_WEIGHTS]
        if self.workers == 1:
            return [_pack_one(t) for t in tasks]
        if self.pool is None:
            self.pool = multiprocessing.get_context("fork").Pool(self.workers)
        return self.pool.map(_pack_one, tasks, chunksize=1)

    def close(self):
        global _PACKING
        if self.pool is not None:
            self.pool.terminate()
            self.pool.join()
        _PACKING = None


def pack(
    count: int,
    sinks: list[str],
    closure: dict[str, frozenset[str]],
    cost: dict[str, float],
    path: dict[str, float],
    reuse: float = 1.0,
    prepared: "_Sinks | None" = None,
) -> tuple[list[float], list[list[str]], list[set[str]]]:
    """`sinks` (largest first) packed into `count` shards: each shard's
    estimated time, its sinks, and the modules it builds. `reuse` weighs
    the work a sink adds to a shard (see `REUSE_WEIGHTS`)."""
    shards: list[set[str]] = [set() for _ in range(count)]
    loads = [0.0] * count
    longest = [0.0] * count
    targets: list[list[str]] = [[] for _ in range(count)]
    # A cold manifest assigns the same default duration to every module.
    # Count those modules instead of looking up and summing every weight
    # again for every target, shard, and candidate count.
    unit = next(iter(cost.values()), 0.0)
    uniform = all(t == unit for t in cost.values())
    if prepared is None:
        prepared = _Sinks(sinks, closure, cost)
    rebuilt, restored = prepared.rebuilt, prepared.restored
    # The restored modules of each shard's sinks, as a bit mask.
    kept = [0] * count
    for s in sinks:
        if uniform:
            added = [unit * len(closure[s] - shard) for shard in shards]
        else:
            added = [sum(map(cost.__getitem__, rebuilt[s] - shard))
                     + UP_TO_DATE * (restored[s] & ~mask).bit_count()
                     for shard, mask in zip(shards, kept)]
        # The work a sink adds counts on its own too, not only through the
        # estimate: a shard whose chain hides it would otherwise take sinks
        # whose imports another shard builds already, and build them again.
        best = min(
            range(count),
            key=lambda i: (estimate(loads[i] + added[i], max(longest[i], path[s])) + reuse * added[i] / PARALLELISM, i),
        )
        shards[best] |= closure[s]
        kept[best] |= restored[s]
        loads[best] += added[best]
        longest[best] = max(longest[best], path[s])
        targets[best].append(s)
    return [estimate(w, p) for w, p in zip(loads, longest)], targets, shards


def refine(imps, closure, cost, path, packed, limit, simulator=None):
    """Move targets to reuse imports, within the chosen latency budget.

    Greedy packing cannot reconsider an early assignment. Rank moves by
    module work saved, reject those whose lower bound exceeds the budget,
    then simulate the two affected shards. Bound the search to 16 attempted
    moves and three accepted moves, independently of project size.
    """
    loads, targets, built = packed
    if simulator is None:
        simulator = _BuildGraph(imps, cost)
    attempts = 0
    for _ in range(3):
        moves = []
        work = [math.fsum(map(cost.__getitem__, part)) for part in built]
        longest = [max((path[t] for t in ts), default=0.0) for ts in targets]
        for src, ts in enumerate(targets):
            if len(ts) < 2:
                continue
            uses = {}
            for t in ts:
                for m in closure[t]:
                    uses[m] = uses.get(m, 0) + 1
            for t in ts:
                removed = {m for m in closure[t] if uses[m] == 1}
                saved = math.fsum(map(cost.__getitem__, removed))
                for dst, part in enumerate(built):
                    if src == dst:
                        continue
                    added = math.fsum(map(cost.__getitem__, closure[t] - part))
                    if saved <= added + 1e-9:
                        continue
                    if estimate(work[dst] + added, max(longest[dst], path[t])) <= limit:
                        moves.append((added - saved, src, dst, t, removed))
        accepted = False
        for _, src, dst, t, removed in sorted(moves, key=lambda m: m[:4]):
            if attempts == 16:
                return loads, targets, built
            attempts += 1
            parts = {src: built[src] - removed, dst: built[dst] | closure[t]}
            times = {i: simulator.time(part) for i, part in parts.items()}
            if max(times.values()) > limit + 1e-9:
                continue
            for i in parts:
                built[i], loads[i] = parts[i], times[i]
            targets[src].remove(t)
            targets[dst].append(t)
            accepted = True
            break
        if not accepted:
            break
    return loads, targets, built


def log_timings(log):
    """Keep module compilation separate from native facets and partial logs."""
    components = {}
    for match in BUILT.finditer(log):
        name, _, facet = match.group(1).partition(":")
        if facet not in ("", *NATIVE_FACETS):
            continue
        duration = float(match.group(2)) / (1000 if match.group(3) == "ms" else 1)
        components.setdefault(name, {})[facet or "lean"] = duration
    return {"version": 1, "components": components}


def update_timings(old, observations, sources, build_inputs, closure=None):
    """One median sample per component per build; retain three same-source samples.

    Partial assembly logs update only their recorded components. Repeated
    shard measurements do not depend on artifact/file order. Changed sources
    and toolchain/options never inherit measurements of the previous build.
    Old flat timing files and manifests remain readable during migration.
    """
    same_inputs = ({k: v for k, v in old.get("inputs", {}).items() if k != "libraries"}
                   == {k: v for k, v in build_inputs.items() if k != "libraries"})
    before = old.get("inputs", {}).get("libraries", {})
    after = build_inputs.get("libraries", {})
    moved = {entry for lib in before.keys() | after.keys()
             for entry in set(before.get(lib, [])) ^ set(after.get(lib, []))}
    old_times = old.get("times", {})
    histories = {}
    times = {}
    for m, source in sources.items():
        if (same_inputs and old.get("sources", {}).get(m) == source
                and not any(matches(entry, m, closure or {}) for entry in moved)):
            if m in old_times:
                times[m] = old_times[m]
            if m in old.get("timing_history", {}):
                histories[m] = {facet: list(values) for facet, values in old["timing_history"][m].items()}
    samples = {}
    for observation in observations:
        if observation.get("version") == 1 and "components" in observation:
            components = observation["components"]
        else:
            components = {m: {"total": value} for m, value in observation.items()}
        for m, facets in components.items():
            if m not in sources:
                continue
            for facet, value in facets.items():
                if facet not in ("lean", "total", *NATIVE_FACETS) or not isinstance(value, (int, float)):
                    raise ValueError(f"Invalid timing component for {m}: {facet}")
                if not math.isfinite(value) or value < 0:
                    raise ValueError(f"Invalid timing duration for {m}: {value}")
                samples.setdefault(m, {}).setdefault(facet, []).append(value)
    for m, facets in samples.items():
        history = histories.setdefault(m, {})
        if "lean" in facets:
            history.pop("total", None)
            facets = {k: v for k, v in facets.items() if k != "total"}
        for facet, values in facets.items():
            if facet == "total" and "lean" in history:
                continue
            history[facet] = [*history.get(facet, []), statistics.median(values)][-3:]
        if "lean" in history:
            times[m] = math.fsum(statistics.median(values) for facet, values in history.items() if facet != "total")
        elif "total" in history:
            times[m] = statistics.median(history["total"])
        # A legacy total cannot be split reliably. Native-only observations
        # keep it until a complete Lean measurement is available.
    return times, histories


def timing_estimates(imps, times, source_bytes=None):
    """Use measured times, or size-matched peers for an unseen module.

    Prefer the nearest namespace with eight measured peers in the same
    power-of-two source-size bucket. The upper quartile allows for expensive
    unseen proofs without assigning every new file a project's typical cost.
    Legacy snapshots without source sizes retain the global median fallback.
    """
    default = sorted(times.values())[len(times) // 2] if times else DEFAULT_TIME
    groups = {}
    for m, t in times.items():
        if m not in imps or m not in (source_bytes or {}):
            continue
        parts = m.split(".")
        bucket = max(1, source_bytes[m]).bit_length() - 1
        for n in range(len(parts)):
            groups.setdefault((".".join(parts[:n]), bucket), []).append(t)
    peers = {k: sorted(v)[int(.75 * (len(v) - 1))]
             for k, v in groups.items() if len(v) >= 8}
    estimates = {}
    for m in imps:
        if m in times:
            estimates[m] = times[m]
            continue
        estimate = default
        if m in (source_bytes or {}):
            parts = m.split(".")
            bucket = max(1, source_bytes[m]).bit_length() - 1
            for n in range(len(parts) - 1, -1, -1):
                key = (".".join(parts[:n]), bucket)
                if key in peers:
                    estimate = peers[key]
                    break
        estimates[m] = estimate
    return estimates, default

def schedule(
    imps: dict[str, list[str]],
    closure: dict[str, frozenset[str]],
    stale: set[str],
    times: dict[str, float],
    diagnostics: dict | None = None,
    *, source_bytes: dict[str, int] | None = None,
    requirements: dict[str, frozenset[str]] | None = None,
) -> tuple[float, dict[str, float], tuple[list[float], list[list[str]], list[set[str]]]]:
    """The shards that build the modules `stale` of the modules `imps`
    (whose import closures are `closure` and whole-library dependencies
    are `requirements`), each taking its time in `times` (an unseen module
    uses size-matched peers when source sizes are available): the work, each module's critical path,
    and each shard's estimated time, its sinks and the modules it builds
    (none when the `lean` job builds them alone)."""
    estimates, default = timing_estimates(imps, times, source_bytes)
    cost = {m: (estimates[m] if m in stale else UP_TO_DATE) for m in imps}
    work = math.fsum(cost[m] for m in stale)
    path = paths(imps, cost)
    required = requirements if requirements is not None else closure
    total = {m: math.fsum(cost[x] for x in required[m]) for m in rebuild_targets(stale, closure)}
    sinks = sorted(total, key=lambda m: (-total[m], m))
    needed = set().union(*(required[m] for m in sinks))
    prepared = _Sinks(sinks, required, cost)
    # Include the same cached imports in the solo estimate as in the shards.
    simulator = _BuildGraph(imps, {m: cost[m] for m in needed})
    solo = simulator.time()
    unique_work = math.fsum(cost[m] for m in needed)
    if diagnostics is not None:
        diagnostics.update({
            "stale_modules": sorted(stale),
            "timed_stale_modules": len(stale & times.keys()),
            "fallback_time_s": default,
            "fallback_estimates": {m: estimates[m] for m in sorted(stale - times.keys())},
            "candidates": [{"shards": 0, "finish_s": solo, "module_work_s": unique_work}],
        })

    def report(packed):
        if diagnostics is not None:
            loads, targets, built = packed
            repeated = math.fsum(cost[m] for part in built for m in part) if built else unique_work
            diagnostics["selected"] = {
                "shards": len(targets),
                "finish_s": max(loads) + SHARD_OVERHEAD if loads else solo,
                "module_work_s": repeated,
                "duplicate_work_s": repeated - unique_work,
            }
            diagnostics["assignments"] = [sorted(part) for part in built]
        return packed

    if solo <= SHARD_OVERHEAD or len(sinks) < 2:
        return work, path, report(([], [], []))
    # Score all useful counts, rather than imposing a work-per-shard cutoff.
    # Include solo in the same latency tolerance: a marginal saving should
    # not buy many runners or repeat most of the build.
    candidates = [(solo, math.fsum(cost[m] for m in needed), 0, ([], [], []))]
    fastest = solo
    # Start with more shards to establish a tight finish-time bound early.
    # A lower bound already outside the tolerance cannot become competitive
    # as the fastest time decreases, so it need not be simulated.
    packings = _Packings(sinks, required, cost, path, prepared)
    for n in range(min(MAX_SHARDS, len(sinks)), 1, -1):
        # However they are packed, n shards build all the work between them,
        # and one builds the longest chain: no packing makes a count whose
        # bound is outside the tolerance competitive.
        if estimate(unique_work / n, max(path[m] for m in sinks)) + SHARD_OVERHEAD > fastest * (1 + SLACK):
            if diagnostics is not None:
                diagnostics["candidates"].append({"shards": n, "excluded": "work_bound"})
            continue
        for reuse, (bounds, targets, built) in zip(REUSE_WEIGHTS, packings(n)):
            candidate = {"shards": n, "reuse": reuse, "lower_bound_finish_s": max(bounds) + SHARD_OVERHEAD}
            if diagnostics is not None:
                diagnostics["candidates"].append(candidate)
            if any(not ts for ts in targets):
                # An empty target list would invoke an unscoped `lake build`.
                candidate["excluded"] = "empty_targets"
                continue
            if max(bounds) + SHARD_OVERHEAD > fastest * (1 + SLACK):
                candidate["excluded"] = "lower_bound"
                continue
            loads = []
            for part in built:
                loads.append(simulator.time(part))
                if loads[-1] + SHARD_OVERHEAD > fastest * (1 + SLACK):
                    break
            if len(loads) != len(built) or max(loads) + SHARD_OVERHEAD > fastest * (1 + SLACK):
                candidate["excluded"] = "simulated_finish"
                continue
            repeated = math.fsum(cost[m] for part in built for m in part)
            candidate.update({"finish_s": max(loads) + SHARD_OVERHEAD, "module_work_s": repeated})
            candidates.append((max(loads) + SHARD_OVERHEAD, repeated, n, (loads, targets, built)))
            fastest = min(fastest, max(loads) + SHARD_OVERHEAD)
    packings.close()
    # Work counts shared dependencies again on each runner. Within the
    # latency tolerance, prefer less work, then fewer runners, then latency.
    # The weights only pack a count's shards: of each count, take the
    # fastest packing (then the least work), so that more weights do not
    # make a slower plan more likely.
    best = {}
    for c in candidates:
        if c[2] not in best or (c[0], c[1]) < (best[c[2]][0], best[c[2]][1]):
            best[c[2]] = c
    chosen = min((c for c in best.values() if c[0] <= fastest * (1 + SLACK)),
                 key=lambda c: (c[1], c[2], c[0]))
    packed = chosen[3]
    if chosen[2]:
        packed = refine(imps, required, cost, path, packed, fastest * (1 + SLACK) - SHARD_OVERHEAD, simulator)
    return work, path, report(packed)


def plan(manifest: dict, diagnostics: dict | None = None) -> dict:
    mods = modules()
    source_bytes, import_modes = {}, {}
    imps, vis, hashes = source_info(mods, source_bytes, import_modes)
    now = inputs()
    if diagnostics is not None:
        diagnostics.update({
            "version": 1,
            "planner_sha256": digest(pathlib.Path(__file__)),
            "manifest_sha256": hashlib.sha256(json.dumps(manifest, sort_keys=True).encode()).hexdigest(),
            "inputs": now,
            "manifest_inputs": manifest.get("inputs", {}),
            "imports": imps,
            "visibility": vis,
            "import_modes": import_modes,
            "historical_times": manifest.get("times", {}),
            "source_bytes": source_bytes,
            "settings": {"max_shards": MAX_SHARDS, "shard_overhead_s": SHARD_OVERHEAD,
                         "slack": SLACK, "parallelism": PARALLELISM, "up_to_date_s": UP_TO_DATE,
                         "default_time_s": DEFAULT_TIME, "fallback_peer_count": 8,
                         "fallback_quantile": .75, "timing_history_samples": 3},
        })
    then = manifest.get("inputs", {})
    sources = manifest.get("sources", {})
    if sources and sources == hashes and now == then:
        # No module, library membership, or other build input changed.
        # Neither invalidation closures nor candidate schedules are needed.
        if diagnostics is not None:
            diagnostics.update({"stale_modules": [], "timed_stale_modules": 0, "candidates": [],
                                "assignments": [], "selected": {"shards": 0, "finish_s": 0.0,
                                "module_work_s": 0.0, "duplicate_work_s": 0.0}})
        return {"stale": 0, "work": 0, "loads": [], "targets": [], "owner": {}, "edited": []}
    closure = closures(imps)
    if {k: v for k, v in then.items() if k != "libraries"} == {k: v for k, v in now.items() if k != "libraries"}:
        changed = {m for m in mods if sources.get(m) != hashes[m]}
        # Modules a library gained or lost.
        old, new = then.get("libraries", {}), now["libraries"]
        moved = {(lib, e) for lib in old.keys() | new.keys() for e in set(old.get(lib, [])) ^ set(new.get(lib, []))}
        changed |= {m for m in mods for _, e in moved if matches(e, m, closure)}
    else:
        changed = set(mods)
    libraries = precompiled_libraries(closure)
    read = reads(imps, closure, vis, import_modes)
    trace_modules = native_trace_modules(closure)
    native = native_reads(imps, closure, libraries, trace_modules)
    stale = stale_of(changed, {m: read[m] | native[m] for m in imps})
    required = build_requirements(closure, libraries)
    if diagnostics is not None:
        diagnostics["precompiled_libraries"] = {name: sorted(ms) for name, ms in libraries.items()}
        diagnostics["native_trace_modules"] = sorted(trace_modules)
    work, _, (estimates, targets, shards) = schedule(imps, closure, stale, manifest.get("times", {}), diagnostics,
                                                        source_bytes=source_bytes, requirements=required)
    owner = {}
    for i, shard in enumerate(shards):
        for m in sorted(shard):
            owner.setdefault(m, i)
    out = {
        "stale": len(stale),
        "work": round(work),
        "loads": [round(t) for t in estimates],
        "targets": [sorted(t) for t in targets],
        "owner": owner,
    }
    # The modules whose sources differ from the last build's, whatever its
    # inputs: what `check_lean_public_imports.py` checks.
    if sources:
        out["edited"] = sorted(m for m in mods if sources.get(m) != hashes[m])
    return out


def shard_index(p: dict, name: str) -> int:
    i = int(name) - 1
    if not 0 <= i < len(p["targets"]):
        raise SystemExit(f"no shard {name}")
    return i


def module_of_output(path: str) -> str:
    """The module whose output `path` is: `lib/lean/A/B.olean.hash` and
    `ir/A/B.c` are outputs of `A.B`."""
    parts = pathlib.PurePosixPath(path).parts[1:]
    if parts and parts[0] == "lean":
        parts = parts[1:]
    return ".".join([*parts[:-1], parts[-1].split(".")[0]]) if parts else ""


def stale_outputs(build: pathlib.Path) -> list[pathlib.Path]:
    """The files under `build` that are outputs of a module of the project's
    libraries that no longer exists. Anything else (outputs of no module, of
    the executables' roots) is kept."""
    mods = modules()
    if not mods:
        raise SystemExit(f"no modules under {LEAN}")
    stale = []
    for f in sorted(build.rglob("*")):
        rel = f.relative_to(build).as_posix()
        if not f.is_file() or rel.split("/")[0] not in ("lib", "ir"):
            continue
        m = module_of_output(rel)
        if any(m == lib or m.startswith(f"{lib}.") for lib in LIBRARIES) and m not in mods:
            stale.append(f)
    return stale


def main(args: list[str]) -> int:
    if len(args) == 3 and args[0] == "plan":
        started = time.monotonic()
        diagnostics = {}
        p = plan(read_json(args[1]), diagnostics)
        diagnostics.update({"planning_s": time.monotonic() - started,
                            "run_id": os.environ.get("GITHUB_RUN_ID"),
                            "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT")})
        p["diagnostics"] = diagnostics
        pathlib.Path(args[2]).write_text(json.dumps(p, indent=1) + "\n")
        count = len(p["targets"])
        print(
            f"{p['stale']} modules to build, about {p['work']} s; shards' estimated times: {p['loads']}",
            file=sys.stderr,
        )
        print(f"count={count}")
        print(f"shards={json.dumps([str(i + 1) for i in range(count)])}")
        return 0
    if len(args) == 3 and args[0] in ("targets", "closure", "outputs"):
        p = read_json(args[1])
        i = shard_index(p, args[2])
        if args[0] == "closure":
            for m in sorted(needed(p["targets"][i], closures(imports(modules())))):
                print(m)
        elif args[0] == "targets":
            # `+`: the module, not the package or library of the same name
            # (`VerifiedGarbage` is all three).
            for m in p["targets"][i]:
                print(f"+{m}")
        else:
            # Outputs of no module (the precompiled libraries' shared
            # libraries) are the first shard's.
            for line in sys.stdin:
                path = line.strip()
                if path and p["owner"].get(module_of_output(path), 0) == i:
                    print(path)
        return 0
    if args in (["times"], ["times", "--observations"]):
        observation = log_timings(sys.stdin.read())
        out = observation if len(args) == 2 else {
            m: math.fsum(facets.values()) for m, facets in observation["components"].items()}
        print(json.dumps(out, indent=1, sort_keys=True))
        return 0
    if len(args) >= 2 and args[0] == "manifest":
        mods = modules()
        sources = {m: digest(f) for m, f in mods.items()}
        build_inputs = inputs()
        old = read_json(args[1])
        closure = (closures(imports(mods)) if old.get("inputs", {}).get("libraries", {})
                   != build_inputs.get("libraries", {}) else None)
        times, history = update_timings(old, [read_json(t) for t in args[2:]],
                                        sources, build_inputs, closure)
        print(json.dumps({"inputs": build_inputs, "sources": sources,
                          "times": times, "timing_history": history}, indent=1))
        return 0
    if len(args) == 2 and args[0] == "prune":
        build = pathlib.Path(args[1])
        stale = stale_outputs(build)
        for f in stale:
            f.unlink()
        # The directories of modules that are gone, deepest first.
        for d in sorted((d for d in build.rglob("*") if d.is_dir()), key=lambda d: -len(d.parts)):
            if not any(d.iterdir()):
                d.rmdir()
        print(f"Deleted {len(stale)} outputs of modules that no longer exist.", file=sys.stderr)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
