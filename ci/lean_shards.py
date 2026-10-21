#!/usr/bin/env python3
"""Plans how CI splits the Lean build across runners.

CI restores the last build `main` saved, and Lake rebuilds only the modules
whose sources changed since, and the modules that read their outputs: those
importing them, and those importing a module that passes them on (`public
import`, `reads`). A module that imports a changed module privately is
rebuilt, but its own outputs come out as they were, so Lake rebuilds nothing
beyond it on its account; the plan counts it among the modules to rebuild
but not what imports it. The build is
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
runner), is the least:
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

For each useful count up to MAX_SHARDS, a dependency-constrained simulation
estimates the packing's build time, including serial phases that cannot
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
  lean_shards.py times                  the time of each module a `lake build`
                                        log on stdin built, as JSON
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
import heapq
import json
import math
import os
import pathlib
import re
import sys
import time
import tomllib

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"
# The libraries of `lean/lakefile.toml`: `VerifiedGarbage.*` (the root module
# and every module under it) and `VerifiedGarbageTest.+` (every module under it).
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


def needed(targets: list[str], closure: dict[str, frozenset[str]]) -> set[str]:
    """The modules a build of `targets` needs built: what they import, and
    every module of a precompiled library one of those is in (Lake links
    the whole library's shared library for a module importing any of its
    modules), with what those import in turn."""
    config = tomllib.loads((LEAN / "lakefile.toml").read_text())
    native = [
        {m for m in closure if any(matches(f"{k}:{e}", m, closure) for k in MODULE_LISTS for e in lib.get(k, []))}
        for lib in config.get("lean_lib", []) if lib.get("precompileModules")
    ]
    out = set().union(*(closure[t] for t in targets))
    grown = True
    while grown:
        grown = False
        for lib in native:
            if out & lib and not lib <= out:
                out |= set().union(*(closure[m] for m in lib))
                grown = True
    return out


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


def import_kinds(text: str, mods) -> list[tuple[bool, bool, str]]:
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


def source_info(mods):
    """Read/hash each source once and share one import scan between graphs.

    Hash the original bytes, but normalize newlines for parsing just as
    Path.read_text does. Sources, imports, and visibility describe the same
    read of each file, including for the final `edited` list.
    """
    imps, vis, hashes = {}, {}, {}
    for m, path in mods.items():
        data = path.read_bytes()
        hashes[m] = hashlib.sha256(data).hexdigest()
        text = data.decode("utf-8")
        if "\r" in text:
            text = text.replace("\r\n", "\n").replace("\r", "\n")
        kinds = import_kinds(text, mods)
        imps[m] = [i for _, _, i in kinds]
        vis[m] = ([i for p, _, i in kinds if p], [i for _, a, i in kinds if a]) if is_module(text) else None
    return imps, vis, hashes


def reads(
    imps: dict[str, list[str]],
    closure: dict[str, frozenset[str]],
    vis: dict[str, tuple[list[str], list[str]] | None],
) -> dict[str, frozenset[str]]:
    """The modules of the project whose outputs each module's build reads
    (its trace), as Lake reads them: each module it imports, and what those
    pass on (`public import`), transitively; with an `import all`, also what
    that module imports; with the whole closure for a file that is not a
    module. A module's public outputs are made from its source and what it
    reads publicly, so a change to a module that a module imports only
    privately (or through a private import) rebuilds the importer, which
    then (but for its own changes) produces the outputs it did, and Lake
    rebuilds nothing beyond it: such a module need not be rebuilt."""
    passed: dict[str, frozenset[str]] = {}
    for root in imps:
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if m in passed:
                continue
            on = imps[m] if vis.get(m) is None else vis[m][0]
            if ready:
                passed[m] = frozenset({m}).union(*(passed[i] for i in on))
            else:
                stack.append((m, True))
                stack += [(i, False) for i in on if i not in passed]
    out = {}
    for m in imps:
        if vis.get(m) is None:
            out[m] = closure[m] - {m}
        else:
            read = set().union(*(passed[i] for i in imps[m]))
            for i in vis[m][1]:
                read |= set().union(*(passed[j] for j in imps[i]))
            out[m] = frozenset(read)
    return out


def stale_of(changed: set[str], read: dict[str, frozenset[str]]) -> set[str]:
    """The modules a build rebuilds when the modules `changed` change: those,
    and every module that reads one of them (`reads`)."""
    return set(changed) | {m for m, r in read.items() if r & changed}


def closures(imps: dict[str, list[str]]) -> dict[str, frozenset[str]]:
    """Each module and everything it imports, directly or not."""
    done: dict[str, frozenset[str]] = {}
    for root in imps:
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if m in done:
                continue
            if ready:
                done[m] = frozenset({m}).union(*(done[i] for i in imps[m]))
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


def pack(
    count: int,
    sinks: list[str],
    closure: dict[str, frozenset[str]],
    cost: dict[str, float],
    path: dict[str, float],
) -> tuple[list[float], list[list[str]], list[set[str]]]:
    """`sinks` (largest first) packed into `count` shards: each shard's
    estimated time, its sinks, and the modules it builds."""
    shards: list[set[str]] = [set() for _ in range(count)]
    loads = [0.0] * count
    longest = [0.0] * count
    targets: list[list[str]] = [[] for _ in range(count)]
    # A cold manifest assigns the same default duration to every module.
    # Count those modules instead of looking up and summing every weight
    # again for every target, shard, and candidate count.
    unit = next(iter(cost.values()), 0.0)
    uniform = all(t == unit for t in cost.values())
    for s in sinks:
        if uniform:
            added = [unit * len(closure[s] - shard) for shard in shards]
        else:
            added = [math.fsum(map(cost.__getitem__, closure[s] - shard)) for shard in shards]
        # The work a sink adds counts on its own too, not only through the
        # estimate: a shard whose chain hides it would otherwise take sinks
        # whose imports another shard builds already, and build them again.
        best = min(
            range(count),
            key=lambda i: (estimate(loads[i] + added[i], max(longest[i], path[s])) + added[i] / PARALLELISM, i),
        )
        shards[best] |= closure[s]
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


def schedule(
    imps: dict[str, list[str]],
    closure: dict[str, frozenset[str]],
    stale: set[str],
    times: dict[str, float],
    diagnostics: dict | None = None,
) -> tuple[float, dict[str, float], tuple[list[float], list[list[str]], list[set[str]]]]:
    """The shards that build the modules `stale` of the modules `imps`
    (whose closures are `closure`), each taking its time in `times` (a
    module without one, the median): the work, each module's critical path,
    and each shard's estimated time, its sinks and the modules it builds
    (none when the `lean` job builds them alone)."""
    default = sorted(times.values())[len(times) // 2] if times else DEFAULT_TIME
    cost = {m: (times.get(m, default) if m in stale else UP_TO_DATE) for m in imps}
    work = math.fsum(cost[m] for m in stale)
    path = paths(imps, cost)
    total = {m: math.fsum(cost[x] for x in closure[m]) for m in rebuild_targets(stale, closure)}
    sinks = sorted(total, key=lambda m: (-total[m], m))
    needed = set().union(*(closure[m] for m in sinks))
    # Include the same cached imports in the solo estimate as in the shards.
    simulator = _BuildGraph(imps, {m: cost[m] for m in needed})
    solo = simulator.time()
    unique_work = math.fsum(cost[m] for m in needed)
    if diagnostics is not None:
        diagnostics.update({
            "stale_modules": sorted(stale),
            "timed_stale_modules": len(stale & times.keys()),
            "fallback_time_s": default,
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
    for n in range(min(MAX_SHARDS, len(sinks)), 1, -1):
        bounds, targets, built = pack(n, sinks, closure, cost, path)
        candidate = {"shards": n, "lower_bound_finish_s": max(bounds) + SHARD_OVERHEAD}
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
    # Work counts shared dependencies again on each runner. Within the
    # latency tolerance, prefer less work, then fewer runners, then latency.
    chosen = min((c for c in candidates if c[0] <= fastest * (1 + SLACK)),
                 key=lambda c: (c[1], c[2], c[0]))
    packed = chosen[3]
    if chosen[2]:
        packed = refine(imps, closure, cost, path, packed, fastest * (1 + SLACK) - SHARD_OVERHEAD, simulator)
    return work, path, report(packed)


def plan(manifest: dict, diagnostics: dict | None = None) -> dict:
    mods = modules()
    imps, vis, hashes = source_info(mods)
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
            "historical_times": manifest.get("times", {}),
            "settings": {"max_shards": MAX_SHARDS, "shard_overhead_s": SHARD_OVERHEAD,
                         "slack": SLACK, "parallelism": PARALLELISM, "up_to_date_s": UP_TO_DATE,
                         "default_time_s": DEFAULT_TIME},
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
    stale = stale_of(changed, reads(imps, closure, vis))
    work, _, (estimates, targets, shards) = schedule(imps, closure, stale, manifest.get("times", {}), diagnostics)
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
    if args == ["times"]:
        times = {}
        for m in BUILT.finditer(sys.stdin.read()):
            # A module of a precompiled library is also compiled to native
            # code and linked (`<module>:c.o`, `<module>:dynlib`), in every
            # shard that builds it: that is part of the module's time. A
            # library's own steps (`NativeTactics:shared`) belong to no module.
            name, _, facet = m.group(1).partition(":")
            if facet in ("", *NATIVE_FACETS):
                t = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
                times[name] = times.get(name, 0.0) + t
        print(json.dumps(times, indent=1, sort_keys=True))
        return 0
    if len(args) >= 2 and args[0] == "manifest":
        mods = modules()
        times = read_json(args[1]).get("times", {})
        for t in args[2:]:
            times.update(read_json(t))
        print(
            json.dumps(
                {
                    "inputs": inputs(),
                    "sources": {m: digest(f) for m, f in mods.items()},
                    "times": {m: times[m] for m in mods if m in times},
                },
                indent=1,
            )
        )
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
