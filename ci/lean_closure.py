#!/usr/bin/env python3
"""What each module's imports cost CI's Lean build, and what a change to
them would save: no builds.

CI's Lean build is split into shards (`lean_shards.py`): each shard builds
the modules that nothing imports ("sinks") it is given, and so everything
they import. A module two shards need is built twice, so an import that
drags a large subtree into a sink costs the build in every shard that gets
that sink, unless the shard builds the subtree anyway. Whether a change to
the imports helps is therefore a question about the plan, not about any one
closure: this answers it with `lean_shards.py`'s own functions.

Module times are the latest Lake `Built` time of each module in the CI
metrics under METRICS (`ci_metrics.py fetch METRICS 30`). Recent runs build
only some modules: the others take the time of their declarations in the
build cache's profile (`lean_profile.py`, which `profile` saves to
METRICS/profile.json once the cache is restored), plus `IMPORT_TIME`, and a
module without either the median.

  lean_closure.py profile [--metrics DIR] [--build DIR]
      save the profile of the restored build cache
  lean_closure.py sinks [--top N] [--metrics DIR]
      the sinks whose closures take the longest to build
  lean_closure.py dominators SINK [--top N] [--metrics DIR]
      the modules of SINK's closure with the time that is in it only
      through each of them (its subtree in the closure's dominator tree):
      what removing that one import would take out of SINK's closure
  lean_closure.py score [--base REF] [--drop A:B ...] [--merge NEW=A,B ...]
                        [--times FILE] [--profile-branch] [--metrics DIR]
                        [--runs N]
      the plan of a full rebuild and of each of the last N runs in METRICS
      that built anything, with the imports of REF (`origin/main`; where
      the branch forked from it, if it is behind) and with
      those of the working tree, with the imports A:B (module A's of B)
      removed: the shards' count, the slowest shard's estimate (and with
      the old count of shards, since a plan within `SLACK` of the fastest
      takes fewer), and the work built more than once (a full rebuild), or
      the modules built and the estimate (each run, which rebuilds what
      imports the modules it built first). The modules whose sources
      differ from REF's take their times on the branch from FILE (a JSON
      object of module names and seconds) or, with --profile-branch, from
      the profile of the build under lean/.lake (after building the branch);
      those without are listed, since they keep REF's time. A module NEW
      that merges the modules A, B, … (NEW among them or not) takes their
      times together, less `IMPORT_TIME` for each but one, and a run that
      built one of them builds NEW.

Every command reads the repository of the working directory (`--repo` for
another).

A plan packs sinks greedily, so a small change can move its estimates by a
few seconds either way: compare a change with the noise, and its effect on
full rebuilds with its effect on the runs.
"""

import argparse
import json
import pathlib
import subprocess
import sys

import lean_profile
import lean_shards as shards

ROOT = shards.LEAN.parent
# What a module takes beyond its declarations' profile (importing, writing
# its outputs): the median difference of the two in CI's metrics.
IMPORT_TIME = 1.25


def run_times(metrics: dict) -> dict[str, float]:
    """The time of each module a run's Lean jobs built."""
    times = {}
    for job in metrics.get("lean", {}).get("jobs", []):
        for built in job.get("built", {}).values():
            times.update(built)
    return times


def load_runs(directory: pathlib.Path) -> list[tuple[str, dict[str, float]]]:
    """Each run under `directory` that built anything, oldest first, with
    the times of the modules it built."""
    runs = []
    for f in sorted(directory.glob("[0-9]*.json"), key=lambda f: int(f.stem) if f.stem.isdigit() else 0):
        times = run_times(json.loads(f.read_text()))
        if times:
            runs.append((f.stem, times))
    return runs


def latest_times(runs: list[tuple[str, dict[str, float]]], profile: dict[str, float]) -> dict[str, float]:
    """Each module's latest time in `runs`, or its time in `profile` (of
    its declarations) and `IMPORT_TIME`."""
    times = {m: t + IMPORT_TIME for m, t in profile.items()}
    for _, t in runs:
        times.update(t)
    return times


def save_profile(build: pathlib.Path, out: pathlib.Path) -> int:
    rows, _, _ = lean_profile.collect(build, [], tests=True)
    profile = {r["module"]: round(lean_profile.total(r), 3) for r in lean_profile.by_module(rows)}
    out.write_text(json.dumps(profile, indent=0, sort_keys=True) + "\n")
    return len(profile)


def use_repo(root: pathlib.Path) -> None:
    """Read the modules of the repository at `root`."""
    global ROOT
    ROOT = root
    shards.LEAN = root / "lean"


def toplevel() -> pathlib.Path:
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    return pathlib.Path(out.stdout.strip()) if out.returncode == 0 else ROOT


def merge_base(ref: str) -> str:
    """The commit the working tree's branch forked from `ref` at."""
    return subprocess.run(["git", "-C", str(ROOT), "merge-base", ref, "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()


def changed_modules(ref: str, mods) -> set[str]:
    """The modules of `mods` whose sources in the working tree differ from
    those at `ref` (or that `ref` lacks)."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "diff", "--name-only", ref, "--", "lean/"],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    out += subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "--others", "--exclude-standard", "--", "lean/"],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    names = {".".join(pathlib.PurePosixPath(f).relative_to("lean").with_suffix("").parts) for f in out}
    return names & set(mods)


def profile_times(build: pathlib.Path, modules: set[str]) -> dict[str, float]:
    """The times of `modules` in the profile of the build under `build`,
    as `latest_times` takes a profile's."""
    if not modules:
        return {}
    rows, _, _ = lean_profile.collect(build, sorted(modules), tests=True)
    return {r["module"]: lean_profile.total(r) + IMPORT_TIME
            for r in lean_profile.by_module(rows) if r["module"] in modules}


def merged(times: dict[str, float], merges: dict[str, list[str]]) -> dict[str, float]:
    """`times` with each module NEW of `merges` taking the times of the
    modules it merges together, less `IMPORT_TIME` for each but one."""
    out = dict(times)
    for new, parts in merges.items():
        ts = [times[m] for m in parts if m in times]
        if ts:
            out[new] = sum(ts) - IMPORT_TIME * (len(ts) - 1)
    return out


def imports_at(ref: str) -> dict[str, list[str]]:
    """The modules of the project at the git revision `ref`, and the
    modules of the project each imports, as `lean_shards.imports` reads them
    from the working tree."""
    names = subprocess.run(
        ["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", ref, "lean/"],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    files = {}
    for name in names:
        rel = pathlib.PurePosixPath(name).relative_to("lean")
        lib = rel.parts[0].removesuffix(".lean")
        if rel.suffix == ".lean" and lib in shards.LIBRARIES and (len(rel.parts) > 1 or shards.LIBRARIES[lib]):
            files[".".join(rel.with_suffix("").parts)] = name
    batch = subprocess.run(
        ["git", "-C", str(ROOT), "cat-file", "--batch"],
        input="".join(f"{ref}:{files[m]}\n" for m in files).encode(), capture_output=True, check=True,
    ).stdout
    imps, pos = {}, 0
    for m in files:
        header_end = batch.index(b"\n", pos)
        size = int(batch[pos:header_end].split()[2])
        imps[m] = shards.imported_by(batch[header_end + 1:header_end + 1 + size].decode(), files)
        pos = header_end + 1 + size + 1
    return dict(sorted(imps.items()))


def sinks_of(imps: dict[str, list[str]]) -> list[str]:
    imported = {i for m in imps for i in imps[m]}
    return [m for m in imps if m not in imported]


def costs(imps, times: dict[str, float]) -> dict[str, float]:
    default = sorted(times.values())[len(times) // 2] if times else shards.DEFAULT_TIME
    return {m: times.get(m, default) for m in imps}


def dominators(imps, sink: str, cost: dict[str, float]) -> dict[str, tuple[float, int, str | None]]:
    """For each module of `sink`'s closure, the time and the number of the
    modules in that closure only through it (itself included), and its
    immediate dominator (the closest module every chain of imports from
    `sink` to it goes through)."""
    order, seen, stack = [], set(), [(sink, False)]
    while stack:
        m, done = stack.pop()
        if done:
            order.append(m)
        elif m not in seen:
            seen.add(m)
            stack.append((m, True))
            stack += [(i, False) for i in imps[m] if i not in seen]
    order.reverse()  # importers before what they import
    importers = {m: [] for m in order}
    for m in order:
        for i in imps[m]:
            importers[i].append(m)
    idom, depth = {sink: None}, {sink: 0}

    def common(a, b):
        while a != b:
            if depth[a] < depth[b]:
                a, b = b, a
            a = idom[a]
        return a

    for m in order[1:]:
        d = importers[m][0]
        for p in importers[m][1:]:
            d = common(d, p)
        idom[m], depth[m] = d, depth[d] + 1
    time = {m: cost[m] for m in order}
    count = dict.fromkeys(order, 1)
    for m in reversed(order[1:]):
        time[idom[m]] += time[m]
        count[idom[m]] += count[m]
    return {m: (time[m], count[m], idom[m]) for m in order}


def first_built(imps, built) -> set[str]:
    """The modules of `built` that import none of the others: those whose
    sources the run changed (or the first it rebuilt for another reason)."""
    return {m for m in built if m in imps and not any(i in built for i in imps[m])}


def full_plan(imps, times, count=None):
    """A full rebuild's plan, and the slowest shard's estimate if it took
    `count` shards (a plan within `SLACK` of the fastest takes fewer)."""
    closure = shards.closures(imps)
    work, path, (loads, _, built) = shards.schedule(imps, closure, set(imps), times)
    cost = costs(imps, times)
    plan = {
        "shards": len(loads),
        "slowest": max(loads, default=0.0),
        "twice": sum(cost[m] for s in built for m in s) - work,
    }
    if count:
        total = {s: sum(cost[m] for m in closure[s]) for s in sinks_of(imps)}
        order = sorted(total, key=lambda s: (-total[s], s))
        plan["slowest_at"] = max(shards.pack(count, order, closure, cost, path)[0])
    return plan


def run_plan(imps, times, changed):
    closure = shards.closures(imps)
    stale = {m for m in imps if closure[m] & changed}
    work, path, (loads, _, _) = shards.schedule(imps, closure, stale, times)
    longest = max((path[m] for m in stale), default=0.0)
    if loads:
        time = max(loads) + shards.SHARD_OVERHEAD
    else:
        time = shards.estimate(work, longest)
    return {"stale": len(stale), "shards": len(loads), "time": time}


def score(base, new, times, runs, branch=None, merges=None):
    """The full rebuild's plans and each run's, with the imports `base` and
    `new`; with `new`, the modules of `branch` take its times, and those of
    `merges` theirs together."""
    branch = branch or {}
    # A merged module the branch has a time for takes that time.
    merges = {m: parts for m, parts in (merges or {}).items() if m not in branch}
    into = {m: new_m for new_m, parts in merges.items() for m in parts}
    b = full_plan(base, times)
    tn = merged({**times, **branch}, merges)
    rows = [("full", {**b, "slowest_at": b["slowest"]}, full_plan(new, tn, b["shards"]))]
    for name, built in runs:
        changed = first_built(base, built)
        run = {**times, **built}
        new_changed = {into.get(m, m) for m in changed} & set(new)
        rows.append((name, run_plan(base, run, changed), run_plan(new, merged({**run, **branch}, merges), new_changed)))
    return rows


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("profile").add_argument("--build", type=pathlib.Path, default=None)
    for name in ("sinks", "dominators", "score"):
        sub.add_parser(name)
    for p in sub.choices.values():
        p.add_argument("--repo", type=pathlib.Path, default=None)
        p.add_argument("--metrics", type=pathlib.Path, default=None)
    for name in ("sinks", "dominators", "score"):
        p = sub.choices[name]
        if name != "score":
            p.add_argument("--top", type=int, default=30)
    sub.choices["dominators"].add_argument("sink")
    sc = sub.choices["score"]
    sc.add_argument("--base", default="origin/main")
    sc.add_argument("--drop", action="append", default=[], metavar="A:B")
    sc.add_argument("--runs", type=int, default=20)
    sc.add_argument("--merge", action="append", default=[], metavar="NEW=A,B")
    sc.add_argument("--times", type=pathlib.Path)
    sc.add_argument("--profile-branch", action="store_true")
    args = parser.parse_args(argv)
    use_repo((args.repo or toplevel()).resolve())
    if args.metrics is None:
        args.metrics = ROOT / ".ci-metrics"

    if args.cmd == "profile":
        args.metrics.mkdir(parents=True, exist_ok=True)
        n = save_profile(args.build or ROOT / "lean/.lake/build/lib/lean", args.metrics / "profile.json")
        print(f"{n} modules' profiles in {args.metrics / 'profile.json'}", file=sys.stderr)
        return 0
    runs = load_runs(args.metrics)
    if not runs:
        raise SystemExit(f"no CI metrics under {args.metrics}: run `ci_metrics.py fetch {args.metrics} 30`")
    saved = args.metrics / "profile.json"
    if not saved.is_file():
        print(f"no {saved}: modules no run built take the median time (see `profile`)", file=sys.stderr)
    times = latest_times(runs, json.loads(saved.read_text()) if saved.is_file() else {})
    mods = shards.modules()
    imps = shards.imports(mods)

    if args.cmd == "sinks":
        closure, cost = shards.closures(imps), costs(imps, times)
        total = {s: sum(cost[m] for m in closure[s]) for s in sinks_of(imps)}
        for s in sorted(total, key=lambda s: (-total[s], s))[:args.top]:
            print(f"{total[s]:7.0f} s {len(closure[s]):5d} modules  {s}")
    elif args.cmd == "dominators":
        if args.sink not in imps:
            raise SystemExit(f"no module {args.sink}")
        dom = dominators(imps, args.sink, costs(imps, times))
        for m in sorted((m for m in dom if m != args.sink), key=lambda m: -dom[m][0])[:args.top]:
            t, n, d = dom[m]
            print(f"{t:7.0f} s {n:5d} modules  {m}  (through {d})")
    else:
        fork = merge_base(args.base)
        base = imports_at(fork)
        new = {m: list(v) for m, v in imps.items()}
        for edge in args.drop:
            a, _, b = edge.partition(":")
            if b not in new.get(a, []):
                raise SystemExit(f"{a} does not import {b}")
            new[a].remove(b)
        merges = {}
        for spec in args.merge:
            target, _, parts = spec.partition("=")
            merges[target] = [p for p in parts.split(",") if p]
            if target not in new:
                raise SystemExit(f"no module {target} in the working tree")
        changed = changed_modules(fork, new)
        branch = {}
        if args.times:
            branch.update({m: t for m, t in json.loads(args.times.read_text()).items() if m in changed})
        if args.profile_branch:
            branch.update(profile_times(ROOT / "lean/.lake/build/lib/lean", changed - set(branch)))
        stale = sorted(changed - set(branch) - set(merges))
        if stale:
            print(f"{len(stale)} modules changed since {args.base} keep its times, or the median if new (--times, --profile-branch):",
                  file=sys.stderr)
            for m in stale:
                print(f"  {m}", file=sys.stderr)
        rows = score(base, new, times, runs[-args.runs:], branch, merges)
        (_, b, n), runs_rows = rows[0], rows[1:]
        print(f"full rebuild: {b['shards']} -> {n['shards']} shards, slowest {b['slowest']:.0f} -> {n['slowest']:.0f} s"
              f" ({n['slowest'] - b['slowest']:+.0f}; {n['slowest_at'] - b['slowest']:+.0f} on {b['shards']} shards),"
              f" built twice {b['twice']:.0f} -> {n['twice']:.0f} s ({n['twice'] - b['twice']:+.0f})")
        for name, b, n in runs_rows:
            print(f"run {name}: {b['stale']} -> {n['stale']} modules, {b['time']:.0f} -> {n['time']:.0f} s"
                  f" ({n['time'] - b['time']:+.0f})")
        if runs_rows:
            delta = sum(n["time"] - b["time"] for _, b, n in runs_rows)
            print(f"{len(runs_rows)} runs: {delta:+.0f} s in all")
    return 0


if __name__ == "__main__":
    sys.exit(main())
