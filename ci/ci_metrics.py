#!/usr/bin/env python3
"""Records what a CI run did and how long it took, for later analysis.

The last steps of every run (`all-green`'s, in ci.yml) collect, into one
JSON file kept as the run's `ci-metrics` artifact for 30 days (unlike the
plan and the shards' outputs, which last a day):

* the run: its event, ref, base ref (a pull request stacked on another's
  branch builds against `main`'s cache, and rebuilds what they differ in),
  commit and attempt;
* every job and step: when it was queued, started and finished, its
  conclusion and its runner;
* the Lean build's full plan, including its exact historical timings,
  assignments, candidate scores, model settings and planner fingerprint;
* each Lean job: the build it restored (a failed or older restore rebuilds
  everything it imports) and, for each step, every module it built and how
  long that took, with native compilation/linking facets recorded separately;
* missing logs/plan artifacts explicitly, and the collector's own fallback
  assembly from its local log when CI_METRICS_ASSEMBLY_LOG is set.

All of it comes from the API and the finished jobs' logs: the plan's line,
each restore's `Cache restored from key:` and Lake's `Built` lines, placed
in their steps by time. It also writes a summary of the Lean build for the
run's page. The short-lived lean-plan artifact is embedded in ci-metrics,
so that the planning inputs survive with the metrics. Old plans and missing
artifacts remain readable; collection never requires a successful build.

  ci_metrics.py collect           the metrics of this run (GH_REPO,
                                  GITHUB_RUN_ID, GITHUB_RUN_ATTEMPT,
                                  BASE_REF), as JSON, with `gh`
  ci_metrics.py summary METRICS   Markdown summarizing METRICS
  ci_metrics.py fetch OUT [LIMIT] download the metrics of the last LIMIT
                                  (100) runs of ci.yml that have them into
                                  OUT/<run>.json, with `gh`, skipping those
                                  there
"""

import concurrent.futures
import datetime
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import zipfile

VERSION = 2
PLAN_JOB = "Lean: plan and build"
SHARD = re.compile(r"Lean: shard \((\d+)\)")
SHARD_BUILD = "Check the shard's proofs"
# Lake's line for a module it built, as lean_shards.py's BUILT (this file
# stands alone: CI fetches it without the repository).
BUILT = re.compile(r"\bBuilt (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")
# Lines of a job's log, each after its timestamp.
LINE = re.compile(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d+)?)Z (.*)$", re.M)
PLAN = re.compile(r"(\d+) modules to build, about (\d+) s; shards' estimated times: \[([^\]]*)\]")
RESTORED = re.compile(r"Cache restored from key: (lean-build-\S+)")
MANIFEST = re.compile(r"Cache restored from key: lean-manifest-(\S+)")
# The restore's own key (the sources' exact build), as its inputs print it.
EXACT = re.compile(r"Z\s+key: (lean-build-\S+)")


def parse_time(t):
    """An API or log timestamp (`…Z`, with fractions of a second or not)."""
    t = t.rstrip("Z")
    if "." in t:
        whole, frac = t.split(".")
        t = f"{whole}.{frac[:6]}"
    return datetime.datetime.fromisoformat(t).replace(tzinfo=datetime.timezone.utc)


def seconds(start, end):
    """The seconds from one API timestamp to another, or None."""
    if not start or not end:
        return None
    return round((parse_time(end) - parse_time(start)).total_seconds())


def job(j):
    return {
        "id": j.get("id"),
        "url": j.get("html_url"),
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
             "started_at": s.get("started_at"), "completed_at": s.get("completed_at"),
             "duration_s": seconds(s.get("started_at"), s.get("completed_at"))}
            for s in j.get("steps", [])
        ],
    }


def built_by_step(log, steps, *, facets=False):
    """For each step of a job, the time of each module the job's log says
    the step built: Lake's `Built` lines, each placed in the step whose
    times (whole seconds, from the API) contain the line's."""
    spans = [(s["name"], parse_time(s["started_at"]), parse_time(s["completed_at"]) + datetime.timedelta(seconds=1))
             for s in steps if s.get("started_at") and s.get("completed_at") and s.get("conclusion") != "skipped"]
    # API timestamps round to seconds. If adjacent steps share a boundary,
    # prefer the step that has just started over the preceding one's grace.
    spans.sort(key=lambda span: span[1], reverse=True)
    out = {}
    for stamp, text in LINE.findall(log):
        m = BUILT.search(text)
        if not m or (":" in m.group(1)) != facets:
            continue
        t = parse_time(stamp)
        step = next((name for name, a, b in spans if a <= t < b), None)
        if step is not None:
            out.setdefault(step, {})[m.group(1)] = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
    return out


def plan_of(log):
    """The plan its job's log states, and the build it is for (the one
    saved with the manifest it restored)."""
    m = PLAN.search(log)
    if not m:
        return None
    manifest = MANIFEST.search(log)
    return {
        "stale": int(m.group(1)),
        "work": int(m.group(2)),
        "estimates": [int(x) for x in m.group(3).split(",") if x.strip()],
        "build": f"lean-build-{manifest.group(1)}" if manifest else None,
    }


def phases(j):
    """Wall times, not summed module CPU work; absent phases stay unknown."""
    names = {"prepare_s": "Run ./.github/actions/lean-prepare",
             "proof_s": SHARD_BUILD, "unpack_s": "Unpack the rest of the build",
             "assemble_s": "Run ./.github/actions/lean-assemble",
             "planning_s": "Run python3 ci/lean_shards.py plan "}
    out = {"queued_s": j["queued_s"]}
    for key, prefix in names.items():
        durations = [s["duration_s"] for s in j["steps"] if s["name"].startswith(prefix)
                     and s["conclusion"] != "skipped" and s["duration_s"] is not None]
        out[key] = sum(durations) if durations else None
    return out


def collect(run, jobs, logs, planning=None):
    """The metrics of a run: its jobs (the API's), and the logs of its Lean
    jobs by name."""
    jobs = [job(j) for j in jobs]
    plan = plan_of(logs.get(PLAN_JOB, ""))
    lean_jobs = []
    for j in jobs:
        if j["name"] not in logs:
            continue
        log = logs[j["name"]]
        restored = RESTORED.findall(log)
        restored = restored[-1] if restored else None
        exact = EXACT.search(log)
        expected = {k for k in ((plan or {}).get("build"), exact and exact.group(1)) if k}
        lean_jobs.append({
            "name": j["name"],
            "job_id": j["id"],
            "phases": phases(j),
            "restored": restored,
            # Whether it restored the plan's build (or the sources' own).
            "restored_planned": (restored in expected) if expected else None,
            "built": built_by_step(log, j["steps"]),
            "facets": built_by_step(log, j["steps"], facets=True),
        })
    built = {}
    for lj in lean_jobs:
        for step, times in lj["built"].items():
            if step.startswith(SHARD_BUILD):
                for m, t in times.items():
                    built.setdefault(m, []).append(t)
    return {
        "version": VERSION,
        "run": {k: run.get(k) for k in (
            "id", "run_attempt", "event", "head_branch", "head_sha", "created_at", "run_started_at", "base_ref")},
        "jobs": jobs,
        "lean": {
            "plan": plan,
            "planning": planning or {"status": "not_collected"},
            "jobs": lean_jobs,
            "missing_logs": [j["name"] for j in jobs if j["name"].startswith("Lean:")
                             and j["conclusion"] != "skipped" and j["completed_at"]
                             and j["name"] not in logs],
            # Module time the shards built more than once.
            "duplicate_work": round(sum(sum(ts) - max(ts) for ts in built.values()), 1),
        },
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
                   f"{len(plan['estimates'])} shards.")
    planning = lean.get("planning", {})
    details = planning.get("plan", {}).get("diagnostics", {})
    if details:
        count = len(details["stale_modules"])
        out.append(f"Historical timings cover {details['timed_stale_modules']}/{count} stale modules. "
                   f"Exact planning inputs and candidate scores are retained in ci-metrics.")
        if planning.get("status") != "available":
            out.append("Retained plan provenance: " + planning["status"] +
                       "; it was not verified as a plan computed in this attempt.")
    elif planning.get("status") == "unavailable":
        out.append("Full planning inputs unavailable; log-derived estimates only.")
    if lean.get("missing_logs"):
        out.append("Missing job logs: " + ", ".join(lean["missing_logs"]) + ".")
    steps = {j["name"]: {s["name"]: s for s in j["steps"]} for j in m["jobs"]}
    rows = []
    order = lambda lj: (int(SHARD.fullmatch(lj["name"]).group(1)) if SHARD.fullmatch(lj["name"]) else 0, lj["name"])
    for lj in sorted(lean["jobs"], key=order):
        ok = {True: "yes", False: f"**no** ({lj['restored'] or 'none'})", None: "–"}[lj["restored_planned"]]
        shard = SHARD.fullmatch(lj["name"])
        for step, times in lj["built"].items():
            estimate = None
            if shard and step.startswith(SHARD_BUILD) and plan and int(shard.group(1)) <= len(plan["estimates"]):
                estimate = plan["estimates"][int(shard.group(1)) - 1]
            rows.append(f"| {lj['name']} | {step} | {fmt(estimate)} | {fmt(steps[lj['name']][step]['duration_s'])} "
                        f"| {len(times)} | {sum(times.values()):.0f} s | {ok} |")
    if rows:
        out += ["", "| Job | Step | Estimate | Took | Modules | Work | Restored the plan's build |",
                "|---|---|---|---|---|---|---|", *rows,
                "", f"The shards built {lean['duplicate_work']:.0f} s of module time more than once."]
    phase_rows = []
    for lj in sorted(lean["jobs"], key=order):
        p = lj.get("phases")
        if p:
            phase_rows.append(f"| {lj['name']} | " + " | ".join(fmt(p[k]) for k in
                              ("queued_s", "prepare_s", "proof_s", "unpack_s", "assemble_s")) + " |")
    if phase_rows:
        out += ["", "### Lean wall time by phase", "",
                "| Job | Queued | Prepare | Shard proofs | Unpack remainder | Assemble |",
                "|---|---|---|---|---|---|", *phase_rows,
                "", "Phase wall times include native work; module/facet durations are recorded separately "
                "and overlap when builds run in parallel."]
    if lean.get("fallback_assembly"):
        a = lean["fallback_assembly"]
        out += ["", f"Fallback assembly in all-green: {len(a['built'])} modules and "
                f"{len(a['facets'])} native facets recorded from the local assembly log."]
    jobs = [j for j in m["jobs"] if j["duration_s"] is not None]
    if jobs:
        out += ["", "## Slowest jobs", "", "| Job | Queued | Ran |", "|---|---|---|"]
        for j in sorted(jobs, key=lambda j: -j["duration_s"])[:10]:
            out.append(f"| {j['name']} | {fmt(j['queued_s'])} | {fmt(j['duration_s'])} |")
    return "\n".join(out) + "\n"


def gh(path, *args):
    return subprocess.run(["gh", "api", *args, path], check=True, capture_output=True).stdout


def fetch_plan(repo, run_id, attempt):
    """Keep the actual plan, not a reconstruction from current sources/cache."""
    try:
        arts = json.loads(gh(f"repos/{repo}/actions/runs/{run_id}/artifacts?name=lean-plan"))["artifacts"]
        arts = [a for a in arts if not a["expired"]]
        if not arts:
            return {"status": "unavailable", "error": "No retained lean-plan artifact"}
        artifact = max(arts, key=lambda a: a["id"])
        data = zipfile.ZipFile(io.BytesIO(gh(f"repos/{repo}/actions/artifacts/{artifact['id']}/zip")))
        plan = json.loads(data.read("lean-plan.json"))
        provenance = plan.get("diagnostics", {})
        if provenance.get("run_id") != str(run_id) or provenance.get("run_attempt") != str(attempt):
            # Rerunning only failed jobs can leave a plan from an older attempt.
            # Retain it, but do not imply that this attempt recomputed it.
            status = "different_attempt" if provenance.get("run_id") == str(run_id) else "unverified"
        else:
            status = "available"
        return {"status": status, "artifact_id": artifact["id"], "plan": plan}
    except (subprocess.CalledProcessError, ValueError, KeyError, zipfile.BadZipFile) as e:
        print(f"No full Lean plan: {e}", file=sys.stderr)
        return {"status": "unavailable", "error": type(e).__name__}


def local_assembly(path):
    """The collector's running job has no downloadable log yet."""
    built, facets = {}, {}
    for m in BUILT.finditer(path.read_text(errors="replace")):
        target = facets if ":" in m.group(1) else built
        target[m.group(1)] = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
    return {"built": built, "facets": facets}


def collect_this_run():
    repo, run_id, attempt = os.environ["GH_REPO"], os.environ["GITHUB_RUN_ID"], os.environ["GITHUB_RUN_ATTEMPT"]
    run = json.loads(gh(f"repos/{repo}/actions/runs/{run_id}")) | {"base_ref": os.environ.get("BASE_REF") or None}
    jobs = [json.loads(line) for line in gh(f"repos/{repo}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100",
                                            "--paginate", "--jq", ".jobs[] | tojson").splitlines()]
    # A skipped job has no log.
    lean = [j for j in jobs if j["name"].startswith("Lean:") and j["status"] == "completed"
            and j.get("conclusion") != "skipped"]

    def log(j):
        path = f"repos/{repo}/actions/jobs/{j['id']}/logs"
        try:
            try:
                return gh(path).decode(errors="replace")
            except subprocess.CalledProcessError as e:
                # Newer `gh` refuses to print Lake's colors without this flag,
                # which older versions reject.
                if b"--allow-escape-sequences" not in e.stderr:
                    raise
                return gh(path, "--allow-escape-sequences").decode(errors="replace")
        except subprocess.CalledProcessError as e:
            # One job's log missing leaves the rest.
            print(f"No log for {j['name']}: {e.stderr.decode(errors='replace').strip()}", file=sys.stderr)
            return None

    # A few MB in all; requests one at a time would wait on each other.
    with concurrent.futures.ThreadPoolExecutor(8) as pool:
        planning = pool.submit(fetch_plan, repo, run_id, attempt)
        logs = {j["name"]: t for j, t in zip(lean, pool.map(log, lean)) if t is not None}
    metrics = collect(run, jobs, logs, planning.result())
    assembly = os.environ.get("CI_METRICS_ASSEMBLY_LOG")
    if assembly and pathlib.Path(assembly).is_file():
        metrics["lean"]["fallback_assembly"] = local_assembly(pathlib.Path(assembly))
    return metrics


def fetch(out, limit, repo="pyca/verified-garbage"):
    out.mkdir(parents=True, exist_ok=True)
    # Keep the page size constant: changing it on the last page changes
    # GitHub's offset, repeating runs and missing the end of the window.
    for offset in range(0, limit, 100):
        runs = json.loads(gh(f"repos/{repo}/actions/workflows/ci.yml/runs?per_page=100&page={offset // 100 + 1}"))
        for run in runs["workflow_runs"][:min(100, limit - offset)]:
            dest = out / f"{run['id']}.json"
            if dest.exists():
                continue
            arts = json.loads(gh(f"repos/{repo}/actions/runs/{run['id']}/artifacts?name=ci-metrics"))["artifacts"]
            arts = [a for a in arts if not a["expired"]]
            if not arts:
                continue
            data = zipfile.ZipFile(io.BytesIO(gh(f"repos/{repo}/actions/artifacts/{arts[0]['id']}/zip")))
            dest.write_bytes(data.read("ci-metrics.json"))
            print(dest, file=sys.stderr)
        if len(runs["workflow_runs"]) < 100:
            break


def main(args):
    if args == ["collect"]:
        print(json.dumps(collect_this_run(), indent=1, sort_keys=True))
        return 0
    if len(args) == 2 and args[0] == "summary":
        sys.stdout.write(summary(json.loads(pathlib.Path(args[1]).read_text())))
        return 0
    if len(args) in (2, 3) and args[0] == "fetch":
        fetch(pathlib.Path(args[1]), int(args[2]) if len(args) == 3 else 100)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
