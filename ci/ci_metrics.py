#!/usr/bin/env python3
"""Records what a CI run did and how long it took, for later analysis.

The last steps of every run (`all-green`'s, in ci.yml) collect, into one JSON
file kept as the run's `ci-metrics` artifact (for the repository's default
retention, unlike the plan and the shards' outputs, which last a day):

* the run: its event, ref, base ref (a pull request stacked on another's
  branch builds against `main`'s cache, and rebuilds what they differ in),
  commit and attempt;
* every job and step: when it was queued, started and finished, its
  conclusion and its runner (from the API);
* the Lean build's plan (`lean_shards.py plan`): what it found stale, its
  estimate of the work, and each shard's sinks and estimated time;
* each shard: the build it restored (a failed or older restore rebuilds
  everything it imports) and how long each module it built took;
* each assembly (`lean-assemble`): the build it restored and each module it
  built (which, with every shard's outputs, should be few).

and writes a summary of the Lean build to the run's page.

  ci_metrics.py shard SHARD PLANNED EXACT RESTORED
                                           a shard's record, from its `lake
                                           build` log on stdin: the build
                                           the plan is for (PLANNED, or
                                           EXACT, the sources' own), the one
                                           it restored (empty if none), and
                                           each module it built
  ci_metrics.py assembly ID RESTORED       an assembly's record, likewise
  ci_metrics.py collect RUN JOBS PLAN DIR  the metrics of the run, as JSON:
                                           RUN and JOBS are the API's run
                                           and its jobs (`.jobs` of every
                                           page, one JSON list), PLAN the
                                           plan (may be missing), DIR the
                                           files the Lean jobs wrote
                                           (`lean-shard-*.json`,
                                           `lean-assembly-*.json`)
  ci_metrics.py summary METRICS            Markdown summarizing METRICS
  ci_metrics.py fetch OUT [LIMIT]          download the metrics of the last
                                           LIMIT (100) runs of ci.yml that
                                           have them into OUT/<run>.json,
                                           with `gh`, skipping those there
"""

import datetime
import io
import json
import pathlib
import subprocess
import sys
import zipfile

import lean_shards

VERSION = 1
REPO = "pyca/verified-garbage"
# The step of a shard that builds its modules.
SHARD_BUILD = "Check the shard's proofs"


def seconds(start, end):
    """The seconds from one API timestamp to another, or None."""
    if not start or not end:
        return None
    parse = lambda t: datetime.datetime.fromisoformat(t.replace("Z", "+00:00"))
    return round((parse(end) - parse(start)).total_seconds())


def job(j):
    return {
        "name": j["name"],
        "conclusion": j.get("conclusion"),
        "runner": j.get("runner_name"),
        "labels": j.get("labels", []),
        "created_at": j.get("created_at"),
        "started_at": j.get("started_at"),
        "completed_at": j.get("completed_at"),
        "queued_s": seconds(j.get("created_at"), j.get("started_at")),
        "duration_s": seconds(j.get("started_at"), j.get("completed_at")),
        "steps": [
            {"name": s["name"], "conclusion": s.get("conclusion"),
             "duration_s": seconds(s.get("started_at"), s.get("completed_at"))}
            for s in j.get("steps", [])
        ],
    }


def times(log):
    """The time of each module a `lake build` log built."""
    return {m.group(1): float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
            for m in lean_shards.BUILT.finditer(log) if ":" not in m.group(1)}


def read_json(path):
    p = pathlib.Path(path)
    return json.loads(p.read_text()) if p.is_file() else None


def collect(run, jobs, plan, records):
    """The metrics of a run: `records` are the files the Lean jobs wrote."""
    jobs = [job(j) for j in jobs]
    shards = sorted((r for r in records if r.get("kind") == "shard"), key=lambda r: int(r["shard"]))
    assemblies = sorted((r for r in records if r.get("kind") == "assembly"), key=lambda r: r["id"])
    by_name = {j["name"]: j for j in jobs}
    built = {}
    for s in shards:
        for m, t in s.get("times", {}).items():
            built.setdefault(m, []).append(t)
    lean = {
        "plan": None if plan is None else {
            "stale": plan.get("stale"),
            "work": plan.get("work"),
            "count": len(plan.get("targets", [])),
            "estimates": plan.get("loads", []),
        },
        "shards": [],
        # Module time built more than once, by several shards.
        "duplicate_work": round(sum(sum(ts) - max(ts) for ts in built.values()), 1),
        "assemblies": [],
    }
    for s in shards:
        i = int(s["shard"])
        built_times = s.get("times", {})
        j = by_name.get(f"Lean: shard ({i})", {})
        step = next((x for x in j.get("steps", []) if x["name"].startswith(SHARD_BUILD)), {})
        estimates = (plan or {}).get("loads", [])
        lean["shards"].append({
            "shard": i,
            "estimate_s": estimates[i - 1] if 0 < i <= len(estimates) else None,
            "build_s": step.get("duration_s"),
            "planned": s.get("planned"),
            "restored": s.get("restored"),
            "restored_planned": s.get("restored") in (s.get("planned"), s.get("exact")) if s.get("planned") else None,
            "modules": len(built_times),
            "work": round(sum(built_times.values()), 1),
            "times": built_times,
        })
    for a in assemblies:
        built_times = a.get("times", {})
        lean["assemblies"].append({
            "id": a["id"],
            "restored": a.get("restored"),
            "modules": len(built_times),
            "work": round(sum(built_times.values()), 1),
            "times": built_times,
        })
    return {
        "version": VERSION,
        "run": {k: run.get(k) for k in (
            "id", "run_attempt", "event", "head_branch", "head_sha", "created_at", "run_started_at")}
               | {"base_ref": run.get("base_ref")},
        "jobs": jobs,
        "lean": lean,
    }


def fmt(s):
    return "–" if s is None else f"{s:.0f} s"


def summary(m):
    lean = m["lean"]
    plan = lean["plan"]
    out = ["## Lean build", ""]
    if plan is None:
        out.append("No plan (the Lean build did not run, or reused another run's outputs).")
    else:
        out.append(f"Plan: {plan['stale']} modules to build, about {plan['work']} s of work, "
                   f"{plan['count']} shards.")
    if lean["shards"]:
        out += ["", "| Shard | Estimate | Build | Modules | Work | Restored the plan's build |",
                "|---|---|---|---|---|---|"]
        for s in lean["shards"]:
            ok = {True: "yes", False: f"**no** ({s['restored'] or 'none'})", None: "–"}[s["restored_planned"]]
            out.append(f"| {s['shard']} | {fmt(s['estimate_s'])} | {fmt(s['build_s'])} | {s['modules']} "
                       f"| {s['work']:.0f} s | {ok} |")
        total = sum(s["work"] for s in lean["shards"])
        out += ["", f"Built {total:.0f} s of module time, {lean['duplicate_work']:.0f} s of it more than once."]
    for a in lean["assemblies"]:
        out.append(f"Assembly ({a['id']}): built {a['modules']} modules, {a['work']:.0f} s"
                   f" (restored {a['restored'] or 'no build'}).")
    jobs = [j for j in m["jobs"] if j["duration_s"] is not None]
    if jobs:
        out += ["", "## Slowest jobs", "", "| Job | Queued | Ran |", "|---|---|---|"]
        for j in sorted(jobs, key=lambda j: -j["duration_s"])[:10]:
            out.append(f"| {j['name']} | {fmt(j['queued_s'])} | {fmt(j['duration_s'])} |")
    return "\n".join(out) + "\n"


def gh(*args):
    return subprocess.run(["gh", "api", *args], check=True, capture_output=True).stdout


def fetch(out, limit):
    out.mkdir(parents=True, exist_ok=True)
    runs = json.loads(gh(f"repos/{REPO}/actions/workflows/ci.yml/runs?per_page={min(limit, 100)}"))
    for run in runs["workflow_runs"][:limit]:
        dest = out / f"{run['id']}.json"
        if dest.exists():
            continue
        arts = json.loads(gh(f"repos/{REPO}/actions/runs/{run['id']}/artifacts?name=ci-metrics"))["artifacts"]
        arts = [a for a in arts if not a["expired"]]
        if not arts:
            continue
        data = zipfile.ZipFile(io.BytesIO(gh(f"repos/{REPO}/actions/artifacts/{arts[0]['id']}/zip")))
        dest.write_bytes(data.read("ci-metrics.json"))
        print(dest, file=sys.stderr)


def main(args):
    if len(args) == 5 and args[0] == "shard":
        record = {"kind": "shard", "shard": args[1], "planned": args[2], "exact": args[3],
                  "restored": args[4], "times": times(sys.stdin.read())}
        print(json.dumps(record, indent=1, sort_keys=True))
        return 0
    if len(args) == 3 and args[0] == "assembly":
        record = {"kind": "assembly", "id": args[1], "restored": args[2], "times": times(sys.stdin.read())}
        print(json.dumps(record, indent=1, sort_keys=True))
        return 0
    if len(args) == 5 and args[0] == "collect":
        records = [json.loads(p.read_text()) for p in sorted(pathlib.Path(args[4]).glob("lean-*.json"))]
        metrics = collect(read_json(args[1]) or {}, read_json(args[2]) or [], read_json(args[3]), records)
        print(json.dumps(metrics, indent=1, sort_keys=True))
        return 0
    if len(args) == 2 and args[0] == "summary":
        sys.stdout.write(summary(read_json(args[1])))
        return 0
    if len(args) in (2, 3) and args[0] == "fetch":
        fetch(pathlib.Path(args[1]), int(args[2]) if len(args) == 3 else 100)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
