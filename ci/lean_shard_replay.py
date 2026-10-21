#!/usr/bin/env python3
"""Compare shard planners on retained CI metrics; no Lean builds.

  python3 ci/lean_shard_replay.py METRICS --baseline-ref REV [--timing observed|prior]

Reads each merge-queue run's exact import graph from local git objects.
Replays its observed rebuilt module set, not an inferred source diff.
With `observed` timing (default), both planners see median module times
from the run itself: a hindsight comparison of partitioning/counts, NOT a
prediction of measured speedups. `prior` uses only observations from Lean
jobs that finished before the run started, falling back to the planner's
median/default for unseen modules. That is not the exact cached manifest.

Both proposed assignments are evaluated using the current build simulator
and observed module times, with the same fixed shard overhead. JSON output
also includes actual shard durations and the simulator's estimates of the
actual assignments. Metrics currently omit native compile/link facets,
so those costs cannot be reconstructed here. Missing git objects are an
error: fetch them before replay, rather than using today's graph.
"""

import argparse
import collections
import json
import math
import pathlib
import statistics
import subprocess
import sys
import time
import types

import lean_closure
import lean_shards as shards


def observations(metrics):
    """Median duration per module across a run's Lean jobs."""
    samples = collections.defaultdict(list)
    for job in metrics["lean"]["jobs"]:
        for step, built in job["built"].items():
            if step.startswith("Check the shard's proofs") or step == "Run ./.github/actions/lean-assemble":
                for module, duration in built.items():
                    samples[module].append(duration)
    return {m: statistics.median(ts) for m, ts in samples.items()}


def evaluate(planner, imps, closure, stale, estimates, observed):
    started = time.monotonic()
    _, _, (_, targets, built) = planner.schedule(imps, closure, stale, estimates)
    planning_s = time.monotonic() - started
    cost = {m: observed[m] if m in stale else shards.UP_TO_DATE for m in imps}
    if not built:
        needed = set().union(*(closure[m] for m in shards.rebuild_targets(stale, closure)))
        built = [needed]
    if not stale <= set().union(*built):
        raise AssertionError("plan does not cover every observed rebuilt module")
    if targets and not all(targets):
        raise AssertionError("empty shard target list")
    loads = [shards.build_time(imps, {m: cost[m] for m in part}) for part in built]
    module_work = math.fsum(cost[m] for part in built for m in part)
    unique_work = math.fsum(cost[m] for m in set().union(*built))
    return {
        "shards": len(targets),
        "build_s": round(max(loads), 3),
        "finish_s": round(max(loads) + (shards.SHARD_OVERHEAD if targets else 0), 3),
        "module_work_s": round(module_work, 3),
        "duplicate_work_s": round(module_work - unique_work, 3),
        "planning_s": round(planning_s, 3),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metrics", type=pathlib.Path)
    parser.add_argument("--baseline-ref", required=True)
    parser.add_argument("--timing", choices=["observed", "prior"], default="observed")
    args = parser.parse_args(argv)
    source = subprocess.run(["git", "show", f"{args.baseline_ref}:ci/lean_shards.py"],
                            check=True, capture_output=True, text=True).stdout
    baseline = types.ModuleType("baseline_lean_shards")
    baseline.__file__ = shards.__file__
    exec(compile(source, f"{args.baseline_ref}:ci/lean_shards.py", "exec"), baseline.__dict__)
    runs = []
    for file in args.metrics.glob("[0-9]*.json"):
        metrics = json.loads(file.read_text())
        if metrics["run"]["event"] != "merge_group" or not metrics["lean"]["plan"]:
            continue
        # A failed or cancelled shard leaves an incomplete observation set.
        jobs = [j for j in metrics["jobs"] if j["name"].startswith("Lean:")
                and j["conclusion"] != "skipped"]
        if any(j["conclusion"] != "success" for j in jobs):
            continue
        ended = max((j["completed_at"] for j in jobs if j["completed_at"]), default=None)
        runs.append((metrics, observations(metrics), ended))
    runs.sort(key=lambda r: (r[0]["run"]["created_at"], r[0]["run"]["id"]))
    rows = []
    for metrics, observed, _ in runs:
        run = metrics["run"]
        imps = lean_closure.imports_at(run["head_sha"])
        closure = shards.closures(imps)
        observed = {m: t for m, t in observed.items() if m in imps}
        stale = set(observed)
        estimates = observed
        if args.timing == "prior":
            estimates = {}
            completed = sorted((end, older["run"]["id"], times)
                               for older, times, end in runs
                               if end and end < run["created_at"])
            for _, _, times in completed:
                estimates.update(times)
        actual = []
        for job in metrics["lean"]["jobs"]:
            api_job = next(j for j in metrics["jobs"] if j["name"] == job["name"])
            for step, built in job["built"].items():
                if step.startswith("Check the shard's proofs"):
                    took = next(s["duration_s"] for s in api_job["steps"] if s["name"] == step)
                    predicted = shards.build_time(imps, {m: t for m, t in built.items() if m in imps})
                    actual.append({"job": job["name"], "actual_s": took, "simulated_s": round(predicted, 3)})
        row = {
            "run": run["id"], "sha": run["head_sha"], "branch": run["head_branch"],
            "planned_stale": metrics["lean"]["plan"]["stale"], "observed_stale": len(stale),
            "known_timing_fraction": round(len(stale & estimates.keys()) / len(stale), 3) if stale else 1,
            "baseline": evaluate(baseline, imps, closure, stale, estimates, observed),
            "proposed": evaluate(shards, imps, closure, stale, estimates, observed),
            "actual_shards": actual,
        }
        rows.append(row)
        print(f"Replayed {run['id']}", file=sys.stderr, flush=True)
    print(json.dumps({"timing": args.timing, "baseline_ref": args.baseline_ref, "runs": rows}, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
