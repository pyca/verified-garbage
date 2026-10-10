#!/usr/bin/env python3
"""Plans how CI splits the Lean build across runners.

CI restores the last build `main` saved, and Lake rebuilds only the modules
whose sources changed since, and the modules importing them. The build is
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
modules that nothing imports ("sinks") it is given, and so everything they
import. A shard's build takes at least its modules' time divided by the
number a runner builds at once, and at least its longest chain of imports
(the "critical path": a module waits for those it imports), so its time is
estimated as the larger of the two. The sinks are packed by the time to
rebuild their imports, largest first, each into the shard where the estimate
it leaves, plus the work it adds there (as time on a runner), is the least:
a shard with a long chain takes other work only until it would finish after
the chain, and a sink goes where much of what it imports is built already,
rather than building it again elsewhere, unless that shard is the slower by
more than the work it saves. A change to the inputs (the toolchain, the
dependencies or the lakefile's settings) rebuilds every module, but not one
that only adds a module to a library or removes one (the lakefile's `globs`
and `roots`): that rebuilds just the modules it moves (and, through their
imports, what imports them). Every module is in exactly one shard (the first
that builds it), so the shards' outputs together are the whole build. A plan
is only an estimate: whatever the shards leave unbuilt, the job that
assembles their outputs (the last shard to finish, normally) builds.

  lean_shards.py plan MANIFEST PLAN     write the plan for the sources (with
                                        the manifest's build, which may be
                                        missing) to PLAN, and print the number
                                        of shards (`count=`) and their names
                                        (`shards=`, a JSON list) for
                                        $GITHUB_OUTPUT
  lean_shards.py targets PLAN SHARD     the sinks of SHARD, as `lake build`
                                        targets (`+Module`), one per line
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
import json
import math
import pathlib
import re
import sys
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
# A shard per this much estimated build time (in seconds of `lake build`'s
# times, which a runner's build runs `PARALLELISM` of at once), up to
# `MAX_SHARDS`. Never just one: a single shard builds nothing in parallel,
# so the `lean` job builds that much itself.
WORK_PER_SHARD = 800.0
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
# How much slower than the fastest plan's slowest shard a plan with fewer
# shards may be.
SLACK = 0.05
# How many modules a runner's build runs at once (as measured: the shards'
# module times add up to 5.4 times their builds' wall times): a shard's
# time is at least its work divided by this.
PARALLELISM = 5.4
# The time to check that a module is up to date, and to build one the
# manifest has no time for when it has none at all.
UP_TO_DATE = 0.02
DEFAULT_TIME = 3.0
IMPORT = re.compile(r"^\s*import\s+(\S+)", re.M)
BUILT = re.compile(r"\bBuilt (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")


def modules() -> dict[str, pathlib.Path]:
    mods = {}
    for lib, root in LIBRARIES.items():
        if root and (LEAN / f"{lib}.lean").is_file():
            mods[lib] = LEAN / f"{lib}.lean"
        for f in (LEAN / lib).rglob("*.lean"):
            mods[".".join(f.relative_to(LEAN).with_suffix("").parts)] = f
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
    return [i for i in IMPORT.findall(text) if i in mods]


def imports(mods: dict[str, pathlib.Path]) -> dict[str, list[str]]:
    """The modules of the project each module imports."""
    return {m: imported_by(f.read_text(), mods) for m, f in mods.items()}


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
    return estimate(sum(cost.values()), max(paths(imps, cost).values(), default=0.0))


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
    for s in sinks:
        added = [sum(cost[x] for x in closure[s] - shard) for shard in shards]
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


def schedule(
    imps: dict[str, list[str]],
    closure: dict[str, frozenset[str]],
    stale: set[str],
    times: dict[str, float],
) -> tuple[float, dict[str, float], tuple[list[float], list[list[str]], list[set[str]]]]:
    """The shards that build the modules `stale` of the modules `imps`
    (whose closures are `closure`), each taking its time in `times` (a
    module without one, the median): the work, each module's critical path,
    and each shard's estimated time, its sinks and the modules it builds
    (none when the `lean` job builds them alone)."""
    default = sorted(times.values())[len(times) // 2] if times else DEFAULT_TIME
    cost = {m: (times.get(m, default) if m in stale else UP_TO_DATE) for m in imps}
    work = sum(cost[m] for m in stale)
    # At most a shard per `WORK_PER_SHARD`; but a sink's closure is built on
    # one runner, so the largest (or the longest chain) may set the time
    # whatever the count. Then more shards only build what they share again:
    # take the fewest whose slowest is within `SLACK` of the fastest plan's.
    most = min(MAX_SHARDS, math.ceil(work / WORK_PER_SHARD))
    # A shard is closed under imports (it builds its sinks' closures), so its
    # critical path is the longest of its sinks'.
    path = paths(imps, cost)
    imported = {i for m in imps for i in imps[m]}
    total = {m: sum(cost[x] for x in closure[m]) for m in imps if m not in imported}
    # Largest first by work, not by estimate: taking long chains first spreads
    # what they import over more shards, which then build it more than once.
    sinks = sorted(total, key=lambda m: (-total[m], m))
    packs = {n: pack(n, sinks, closure, cost, path) for n in range(2, most + 1)}
    best = min((max(p[0]) for p in packs.values()), default=0.0)
    count = min((n for n, p in packs.items() if max(p[0]) <= best * (1 + SLACK)), default=0)
    # Unless the `lean` job would build it all about as fast itself.
    if count and max(packs[count][0]) + SHARD_OVERHEAD > estimate(work, max(path.values(), default=0.0)):
        count = 0
    return work, path, packs[count] if count else ([], [], [])


def plan(manifest: dict) -> dict:
    mods = modules()
    imps = imports(mods)
    closure = closures(imps)
    now = inputs()
    then = manifest.get("inputs", {})
    sources = manifest.get("sources", {})
    if {k: v for k, v in then.items() if k != "libraries"} == {k: v for k, v in now.items() if k != "libraries"}:
        changed = {m for m, f in mods.items() if sources.get(m) != digest(f)}
        # Modules a library gained or lost.
        old, new = then.get("libraries", {}), now["libraries"]
        moved = {(lib, e) for lib in old.keys() | new.keys() for e in set(old.get(lib, [])) ^ set(new.get(lib, []))}
        changed |= {m for m in mods for _, e in moved if matches(e, m, closure)}
    else:
        changed = set(mods)
    stale = {m for m in mods if closure[m] & changed}
    work, _, (loads, targets, shards) = schedule(imps, closure, stale, manifest.get("times", {}))
    owner = {}
    for i, shard in enumerate(shards):
        for m in sorted(shard):
            owner.setdefault(m, i)
    return {
        "stale": len(stale),
        "work": round(work),
        "loads": [round(t) for t in loads],
        "targets": [sorted(t) for t in targets],
        "owner": owner,
    }


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
        p = plan(read_json(args[1]))
        pathlib.Path(args[2]).write_text(json.dumps(p, indent=1) + "\n")
        count = len(p["targets"])
        print(
            f"{p['stale']} modules to build, about {p['work']} s; shards' estimated times: {p['loads']}",
            file=sys.stderr,
        )
        print(f"count={count}")
        print(f"shards={json.dumps([str(i + 1) for i in range(count)])}")
        return 0
    if len(args) == 3 and args[0] in ("targets", "outputs"):
        p = read_json(args[1])
        i = shard_index(p, args[2])
        if args[0] == "targets":
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
            if ":" not in m.group(1):
                times[m.group(1)] = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
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
