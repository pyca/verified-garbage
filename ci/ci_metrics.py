#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
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
* Rust timed test observations and per-feature-line CPU/wall times from logs;
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
                                  there; --hours or --start/--end select a
                                  creation-time window instead of a count
  ci_metrics.py bundle OUT --output FILE.json.gz
                                  export the last fetch selection for sharing

See ci/metrics-analysis.md for collection, transport, and analysis guidance.
"""

import argparse
import concurrent.futures
import datetime
import gzip
import io
import itertools
import json
import math
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import zipfile
import time
from urllib.parse import urlencode

VERSION = 3
COLLECT_DEADLINE = None
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
# The build a plan is for, when lean_reuse.py chose it (it may be another
# run's base's), after the plans it compared.
BUILDS_ON = re.compile(r"The plan builds on (lean-build-\S+)\.")
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
        "status": j.get("status"),
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
    """The plan its job's log states (the last: lean_reuse.py states the
    one it chose after those it compared), and the build it is for (the
    one it states, or the one saved with the manifest it restored)."""
    plans = list(PLAN.finditer(log))
    if not plans:
        return None
    m = plans[-1]
    builds_on = BUILDS_ON.search(log)
    manifest = MANIFEST.search(log)
    return {
        "stale": int(m.group(1)),
        "work": int(m.group(2)),
        "estimates": [int(x) for x in m.group(3).split(",") if x.strip()],
        "build": (builds_on.group(1) if builds_on
                  else f"lean-build-{manifest.group(1)}" if manifest else None),
    }


def phases(j):
    """Wall times, not summed module CPU work; absent phases stay unknown."""
    names = {"prepare_s": "Run ./.github/actions/lean-prepare",
             "proof_s": SHARD_BUILD, "unpack_s": "Unpack the rest of the build",
             "assemble_s": "Run ./.github/actions/lean-assemble",
             "planning_s": ("Run python3 ci/lean_shards.py plan ", "Run python3 ci/lean_reuse.py select ")}
    out = {"queued_s": j["queued_s"]}
    for key, prefix in names.items():
        durations = [s["duration_s"] for s in j["steps"] if s["name"].startswith(prefix)
                     and s["conclusion"] != "skipped" and s["duration_s"] is not None]
        out[key] = sum(durations) if durations else None
    return out


# libtest --report-time output (optional until all jobs enable it). Keep
# repeated names: binaries, feature lines and steps may run the same test.
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
TEST_TIME = re.compile(r"^test (.+?) \.\.\. (ok|FAILED|ignored) <(\d+(?:\.\d+)?)s>$")
CPU_TIME = re.compile(r"^VG_CPU_FEATURES=(.*?): (.*): (\d+(?:\.\d+)?) (\d+(?:\.\d+)?) s of CPU \(user, system\)$")
FEATURE_WALL = re.compile(r"^CI_FEATURE_TIME_V1 (\d+) (\d+) (\d+) (-?\d+) (\d+)$")


def rust_metrics(j, log):
    tests, runs = [], []
    feature_line, binary = None, None
    spans = [(s["name"], parse_time(s["started_at"]), parse_time(s["completed_at"]) + datetime.timedelta(seconds=1))
             for s in j["steps"] if s.get("started_at") and s.get("completed_at")
             and s.get("conclusion") != "skipped"]
    spans.sort(key=lambda s: s[1], reverse=True)
    current_step = None
    command_step = False
    binaries, block = [], -1
    for stamp, text in LINE.findall(ANSI.sub("", log)):
        t = parse_time(stamp)
        header = text.startswith(("##[group]Run ", "::group::Run "))
        step = next((name for name, a, b in spans if a <= t < b), None)
        # API timestamps are whole seconds: buffered output can share the
        # next step's start second. Runner command headers preserve ordering.
        if header and spans:
            # The runner's command header can precede the API's rounded
            # start by a fraction of a second. Prefer that adjacent start.
            command = text.removeprefix("##[group]").removeprefix("::group::")
            nearby = [span for span in spans if abs((span[1] - t).total_seconds()) < 1]
            exact = [span for span in nearby if span[0] == command]
            nearest = min(exact or nearby or spans,
                          key=lambda span: (abs((span[1] - t).total_seconds()),
                                            -(span[2] - span[1]).total_seconds()))
            if abs((nearest[1] - t).total_seconds()) < 1:
                step = nearest[0]
        if header or (not command_step and step != current_step):
            feature_line, binary = None, None
            binaries, block = [], -1
            current_step = step
            command_step = command_step or header
        step = current_step
        if text.startswith(("::group::VG_CPU_FEATURES=", "##[group]VG_CPU_FEATURES=")):
            feature_line = text.removeprefix("::group::").removeprefix("##[group]")
            binary, binaries, block = None, [], -1
        elif text in ("::endgroup::", "##[endgroup]") and feature_line is not None:
            feature_line, binary = None, None
            binaries, block = [], -1
        if re.match(r"^\s*(?:Running (?:unittests |tests[/\\])|Doc-tests )", text):
            binaries.append(text.strip())
        if re.fullmatch(r"running \d+ tests?", text.strip()):
            # Cargo headers use stderr; piped test stdout can arrive after
            # several headers. Match stdout blocks to headers in order.
            block += 1
        binary = binaries[block] if 0 <= block < len(binaries) else None
        m = TEST_TIME.fullmatch(text.strip())
        if m:
            tests.append({"name": m[1], "outcome": m[2], "elapsed_s": float(m[3]),
                          "binary": binary, "feature_line": feature_line, "step": step})
        m = CPU_TIME.fullmatch(text)
        if m:
            runs.append({"features": m[1], "groups": m[2].split(), "user_s": float(m[3]),
                         "system_s": float(m[4]), "start_offset_s": None, "wall_s": None,
                         "exit_code": None})
        m = FEATURE_WALL.fullmatch(text)
        if m and runs:
            # Records are printed immediately after the corresponding CPU line.
            index, start, end, origin, status = map(int, m.groups())
            if index == len(runs) - 1 and end >= start >= origin:
                runs[-1].update(start_offset_s=(start - origin) / 1000000,
                                wall_s=(end - start) / 1000000, exit_code=status)
    return {"job_id": j["id"], "name": j["name"], "tests": tests, "feature_runs": runs}


def rebuild_check(lean_jobs, planning):
    """Compare observed compilations with a verified same-attempt stale set.

    Missing logs remain unknown; native facets are not module rebuilds.
    This records discrepancies without guessing why Lake rebuilt a module.
    """
    diagnostics = (planning or {}).get("plan", {}).get("diagnostics", {})
    if (planning or {}).get("status") != "available" or "stale_modules" not in diagnostics:
        return {"status": "unavailable"}
    stale = set(diagnostics["stale_modules"])
    rows = []
    for j in lean_jobs:
        unexpected = {
            step: {m: t for m, t in built.items() if m not in stale}
            for step, built in j["built"].items()
            if step.startswith(SHARD_BUILD) or step == "Run ./.github/actions/lean-assemble"
        }
        unexpected = {step: built for step, built in unexpected.items() if built}
        if unexpected:
            rows.append({"job_id": j["job_id"], "name": j["name"],
                         "restored_planned": j["restored_planned"], "unexpected": unexpected})
    return {"status": "available", "jobs": rows}


def collect(run, jobs, logs, planning=None):
    """The metrics of a run: its jobs (the API's), and the logs of its Lean
    and Rust jobs by name."""
    jobs = [job(j) for j in jobs]
    plan = plan_of(logs.get(PLAN_JOB, ""))
    lean_jobs = []
    for j in jobs:
        if not j["name"].startswith("Lean:") or j["name"] not in logs:
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
        "collection": {
            "collected_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "jobs_complete": all(j["completed_at"] is not None for j in jobs),
            "unfinished_job_ids": [j["id"] for j in jobs if not j["completed_at"]],
            "finished_runner_s": sum(j["duration_s"] for j in jobs
                                     if j["duration_s"] is not None and j["conclusion"] != "skipped"),
            "missing_log_job_ids": [j["id"] for j in jobs
                                    if j["name"].startswith(("Lean:", "Rust ("))
                                    and (not j["name"].startswith("Rust (") or run.get("event") != "push")
                                    and j["completed_at"] and j["conclusion"] != "skipped"
                                    and j["name"] not in logs],
        },
        "rust": {"jobs": [rust_metrics(j, logs[j["name"]]) for j in jobs
                          if j["name"].startswith("Rust (") and j["name"] in logs]},
        "lean": {
            "rebuild_check": rebuild_check(lean_jobs, planning),
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
    check = lean.get("rebuild_check", {})
    if check.get("status") == "available":
        unexpected = [built for j in check["jobs"] for built in j["unexpected"].values()]
        count = sum(len(built) for built in unexpected)
        work = sum(sum(built.values()) for built in unexpected)
        out.append(f"Observed rebuilds outside the planned stale set: {count} module observations, "
                   f"{work:.0f} s of summed module duration (not elapsed time).")
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
    rust = m.get("rust", {}).get("jobs", [])
    if rust:
        out += ["", "## Rust timings", "",
                "| Job | Timed test observations | Feature lines | Feature CPU time |",
                "|---|---|---|---|"]
        for j in rust:
            cpu = sum(r["user_s"] + r["system_s"] for r in j["feature_runs"])
            out.append(f"| {j['name']} | {len(j['tests'])} | {len(j['feature_runs'])} | {fmt(cpu)} |")
        out += ["", "Test observations include only elapsed times present in logs; absent timings are unknown."]
    if "collection" in m:
        c = m["collection"]
        out += ["", f"Finished jobs used {fmt(c['finished_runner_s'])} of runner time (not billed time). "
                "This snapshot excludes unfinished jobs, including this collector's final duration."]
        if c["missing_log_job_ids"]:
            out.append("Missing logs for job IDs: " + ", ".join(map(str, c["missing_log_job_ids"])) + ".")
    return "\n".join(out) + "\n"


def gh(path, *args, output=None):
    timeout = None if COLLECT_DEADLINE is None else max(0.001, min(5, COLLECT_DEADLINE - time.monotonic()))
    streams = {"capture_output": True} if output is None else {"stdout": output, "stderr": subprocess.PIPE}
    return subprocess.run(["gh", "api", *args, path], check=True, timeout=timeout, **streams).stdout


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
    except (subprocess.CalledProcessError, ValueError, KeyError, zipfile.BadZipFile, subprocess.TimeoutExpired) as e:
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
    # Leave headroom inside ci.yml's unchanged 30-second timeout to serialize
    # and upload a partial observation even when individual log requests stall.
    global COLLECT_DEADLINE
    COLLECT_DEADLINE = time.monotonic() + 22
    try:
        return _collect_this_run()
    finally:
        COLLECT_DEADLINE = None


def _collect_this_run():
    repo, run_id, attempt = os.environ["GH_REPO"], os.environ["GITHUB_RUN_ID"], os.environ["GITHUB_RUN_ATTEMPT"]
    run = json.loads(gh(f"repos/{repo}/actions/runs/{run_id}")) | {"base_ref": os.environ.get("BASE_REF") or None}
    jobs = [json.loads(line) for line in gh(f"repos/{repo}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100",
                                            "--paginate", "--jq", ".jobs[] | tojson").splitlines()]
    # A skipped job has no log.
    finished = [j for j in jobs
                if (j["name"].startswith("Lean:")
                    or (j["name"].startswith("Rust (") and run.get("event") != "push"))
                and j["status"] == "completed" and j.get("conclusion") != "skipped"]

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
        except subprocess.TimeoutExpired:
            print(f"No log for {j['name']}: collection deadline/request timeout", file=sys.stderr)
            return None
        except subprocess.CalledProcessError as e:
            # One job's log missing leaves the rest.
            print(f"No log for {j['name']}: {e.stderr.decode(errors='replace').strip()}", file=sys.stderr)
            return None

    # Reuse one bounded pool for Lean and Rust; requests share the deadline.
    with concurrent.futures.ThreadPoolExecutor(8) as pool:
        planning = pool.submit(fetch_plan, repo, run_id, attempt)
        logs = {j["name"]: t for j, t in zip(finished, pool.map(log, finished)) if t is not None}
    metrics = collect(run, jobs, logs, planning.result())
    assembly = os.environ.get("CI_METRICS_ASSEMBLY_LOG")
    if assembly and pathlib.Path(assembly).is_file():
        metrics["lean"]["fallback_assembly"] = local_assembly(pathlib.Path(assembly))
    return metrics


RUN_FIELDS = ("id", "html_url", "head_sha", "head_branch", "event", "created_at",
              "status", "conclusion", "run_attempt")
FETCH_ERRORS = (OSError, ValueError, KeyError, RuntimeError, zipfile.BadZipFile,
                OverflowError, subprocess.CalledProcessError, subprocess.TimeoutExpired)


def fetch_error(error):
    """gh redirect errors can contain signed storage credentials in the URL."""
    text = (error.stderr.decode(errors="replace") if isinstance(error, subprocess.CalledProcessError)
            and error.stderr else str(error))
    return re.sub(r'(https?://[^\s?"\\]+)\?[^\s"\\]+', r'\1?[redacted]', text).strip()


def fetch_pages(endpoint, key, filtered=False):
    page = 1
    while True:
        separator = "&" if "?" in endpoint else "?"
        data = json.loads(gh(f"{endpoint}{separator}per_page=100&page={page}"))
        if filtered and data["total_count"] > 1000:
            raise ValueError("GitHub limits filtered run searches to 1000 results; use a smaller time window")
        yield from data[key]
        if len(data[key]) < 100:
            return
        page += 1


def utc_stamp(value):
    return value.astimezone(datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def write_collection(path, data):
    """Replace the selection/state atomically, leaving metrics files intact."""
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     prefix=".collection-", delete=False) as stream:
        temporary = pathlib.Path(stream.name)
        try:
            json.dump(data, stream, indent=2)
            stream.write("\n")
        except BaseException:
            stream.close()
            temporary.unlink(missing_ok=True)
            raise
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def download_metrics(base, artifact, dest):
    # The ZIP is spooled to disk. Parse only this artifact, retaining its
    # embedded provenance; copy the original metrics bytes to the cache.
    with tempfile.TemporaryFile() as packed:
        gh(f"{base}/artifacts/{artifact['id']}/zip", output=packed)
        packed.seek(0)
        with zipfile.ZipFile(packed) as archive:
            with archive.open("ci-metrics.json") as source:
                document = json.load(source)
            if not isinstance(document, dict):
                raise ValueError("ci-metrics.json must be an object")
            embedded_run = document.get("run")
            del document
            target = dest.open("xb")
            try:
                with target, archive.open("ci-metrics.json") as source:
                    while block := source.read(1024 * 1024):
                        target.write(block)
            except BaseException:
                dest.unlink(missing_ok=True)
                raise
    return embedded_run


def fetch(out, limit=None, repo="pyca/verified-garbage", *, hours=None, start=None, end=None, workflow="ci.yml"):
    """Resume individual files and record the current selection in collection.json.

    cached_runs retains provenance across selections; runs contains only this
    invocation's successful/cached entries. Export uses runs, never all files
    left over in OUT from earlier windows.
    """
    window = hours is not None or start is not None or end is not None
    if window:
        if limit is not None:
            raise ValueError("a run-count limit cannot be combined with a time window")
        if hours is None and start is None:
            raise ValueError("--end requires --hours or --start")
        if hours is not None and start is not None:
            raise ValueError("choose --hours or --start")
        end = end or datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
        start = start or end - datetime.timedelta(hours=hours)
        if start.tzinfo is None or end.tzinfo is None or start >= end:
            raise ValueError("start and end must include timezones, with start before end")
    else:
        limit = 100 if limit is None else limit
        if limit <= 0:
            raise ValueError("run-count limit must be positive")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo):
        raise ValueError("repository must be owner/repo")
    out.mkdir(parents=True, exist_ok=True)
    state = out / "collection.json"
    previous = json.loads(state.read_text()) if state.exists() else {}
    if previous and (previous.get("schema_version") != 1 or previous.get("repository") != repo
                     or previous.get("workflow") != workflow):
        raise ValueError("collection directory belongs to a different repository/workflow or unsupported schema")
    collection = {"schema_version": 1, "repository": repo, "workflow": workflow,
                  "start": utc_stamp(start) if start else None, "end": utc_stamp(end) if end else None,
                  "limit": limit, "window_basis": "workflow run created_at" if window else "recent workflow run count",
                  "downloaded_at": utc_stamp(datetime.datetime.now(datetime.timezone.utc)),
                  "selection_complete": False, "inspected_runs": 0, "runs": [], "missing": [], "errors": [],
                  "cached_runs": previous.get("cached_runs", {})}
    base = f"repos/{repo}/actions"
    endpoint = f"{base}/workflows/{workflow}/runs"
    if window:
        endpoint += "?" + urlencode({"created": f"{utc_stamp(start)}..{utc_stamp(end)}"})
    try:
        runs = fetch_pages(endpoint, "workflow_runs", filtered=window)
        for run in itertools.islice(runs, limit):
            collection["inspected_runs"] += 1
            meta = {k: run.get(k) for k in RUN_FIELDS}
            run_id = str(int(run["id"]))
            dest = out / f"{run_id}.json"
            artifact = None
            try:
                if dest.exists():
                    old = collection["cached_runs"].get(run_id, {})
                    row = old | {"run": meta, "file": dest.name, "cached": True,
                                 "provenance": old.get("provenance", "legacy_local"),
                                 "artifact_id": old.get("artifact_id")}
                else:
                    arts = [a for a in fetch_pages(f"{base}/runs/{run_id}/artifacts?name=ci-metrics", "artifacts")
                            if a["name"] == "ci-metrics"]
                    retained = [a for a in arts if not a.get("expired")]
                    if not retained:
                        collection["missing"].append({"run": meta, "reason": "Only expired ci-metrics artifacts" if arts
                                                      else "No ci-metrics artifact"})
                        continue
                    artifact = max(retained, key=lambda a: a["id"])
                    embedded_run = download_metrics(base, artifact, dest)
                    row = {"run": meta, "downloaded_run": meta, "metrics_run": embedded_run,
                           "downloaded_at": utc_stamp(datetime.datetime.now(datetime.timezone.utc)),
                           "file": dest.name, "artifact_id": artifact["id"], "cached": False,
                           "provenance": "downloaded", "artifact": artifact}
                    print(dest, file=sys.stderr)
                collection["runs"].append(row)
                collection["cached_runs"][run_id] = row
            except FETCH_ERRORS as error:
                failure = {"run": meta, "error": fetch_error(error)}
                if artifact is not None:
                    failure["artifact_id"] = artifact["id"]
                collection["errors"].append(failure)
                print(f"Run {run_id}: {failure['error']}", file=sys.stderr)
        collection["selection_complete"] = True
    except FETCH_ERRORS as error:
        collection["errors"].append({"stage": "list_runs", "error": fetch_error(error)})
    finally:
        write_collection(state, collection)
    print(f"Inspected {collection['inspected_runs']} runs; {len(collection['runs'])} local metrics; "
          f"{len(collection['missing'])} missing; {len(collection['errors'])} errors. See {state}", file=sys.stderr)
    return 1 if collection["errors"] else 0


def bundle(out, output):
    """Export the last fetch selection, one metrics document at a time."""
    if output.suffix != ".gz":
        raise ValueError("bundle output must end in .gz")
    collection = json.loads((out / "collection.json").read_text())
    if collection.get("schema_version") != 1:
        raise ValueError("unsupported collection schema")
    header = {k: v for k, v in collection.items() if k not in ("cached_runs", "runs")}
    output.parent.mkdir(parents=True, exist_ok=True)
    raw = output.open("xb")
    try:
        with raw, gzip.open(raw, "wt", encoding="utf-8", compresslevel=6) as stream:
            stream.write(json.dumps(header)[:-1] + ',"runs":[')
            for index, row in enumerate(collection["runs"]):
                name = f"{int(row['run']['id'])}.json"
                if row["file"] != name:
                    raise ValueError("collection metrics filenames must match their run IDs")
                document = json.loads((out / name).read_bytes())
                if not isinstance(document, dict):
                    raise ValueError(f"{name} must be a metrics object")
                if index:
                    stream.write(",")
                json.dump({k: v for k, v in row.items() if k != "file"} |
                          {"files": {"ci-metrics.json": document}}, stream, separators=(",", ":"))
                del document
            stream.write("]}\n")
    except BaseException:
        output.unlink(missing_ok=True)
        raise


def fetch_timestamp(value):
    try:
        result = datetime.datetime.fromisoformat(value.replace("Z", "+00:00"))
        if result.tzinfo is None:
            raise ValueError("include a timezone, for example 2026-10-21T12:00:00Z")
        return result.astimezone(datetime.timezone.utc)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def positive_hours(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError("hours must be positive and finite")
    return number


def fetch_command(args):
    parser = argparse.ArgumentParser(prog="ci_metrics.py fetch")
    parser.add_argument("out", type=pathlib.Path)
    parser.add_argument("limit", nargs="?", type=int, help="recent runs to inspect (default: 100)")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--hours", type=positive_hours)
    selection.add_argument("--start", type=fetch_timestamp)
    parser.add_argument("--end", type=fetch_timestamp)
    parser.add_argument("--repository", "--repo", default="pyca/verified-garbage")
    parser.add_argument("--workflow", default="ci.yml")
    options = parser.parse_args(args)
    try:
        return fetch(options.out, options.limit, options.repository, hours=options.hours,
                     start=options.start, end=options.end, workflow=options.workflow)
    except FETCH_ERRORS as error:
        parser.exit(1, f"Error: {fetch_error(error)}\n")


def main(args):
    if args == ["collect"]:
        print(json.dumps(collect_this_run(), indent=1, sort_keys=True))
        return 0
    if len(args) == 2 and args[0] == "summary":
        sys.stdout.write(summary(json.loads(pathlib.Path(args[1]).read_text())))
        return 0
    if args and args[0] == "fetch":
        return fetch_command(args[1:])
    if args and args[0] == "bundle":
        parser = argparse.ArgumentParser(prog="ci_metrics.py bundle")
        parser.add_argument("out", type=pathlib.Path)
        parser.add_argument("--output", type=pathlib.Path, required=True)
        options = parser.parse_args(args[1:])
        try:
            bundle(options.out, options.output)
        except FETCH_ERRORS as error:
            parser.exit(1, f"Error: {fetch_error(error)}\n")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
