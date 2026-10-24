#!/usr/bin/env python3
"""Builds the Lean proofs on top of the merge queue's run of the base commit.

CI restores the last build `main` saved, and plans what to rebuild against
its manifest (`lean_shards.py`). Until a push to main has saved a newer
build, every run starts from the older one: after a change that rebuilds
most of the project (one to `TCB/Sig.lean`, say), each merge queue entry
queued behind it, each pull request opened on top of it, and the push to
main all rebuild the whole project again, on twelve runners each. The
merge queue's run of that commit has built it already, and its outputs (the
shards' `lean-build-<n>` and the assembly's `lean-build-final-<id>`, kept
for a day) are what a build of the commit adds to the build it restored.
So a run builds on top of them, as the push to main always did.

The run whose outputs a run reuses (its base run) is the merge queue's run
of its base commit: for a push to main, the commit itself (the commit the
merge queue tested, which GitHub moves main to); for a pull request, its
merge commit's first parent (main); for a merge queue entry, its first
parent (the entry ahead of it, or main). Only merge queue runs are ever
reused: their code is what main is about to be, and no pull request's
outputs reach any other run. A base run may itself have reused its own
base run's outputs: each merge queue run uploads `lean-base`, the build of
`main` it restored (its manifest's cache key) and the runs whose outputs it
added to it, in order, and a run reusing it restores that build and adds
those runs' outputs, then the base run's own. Lake checks every module
against its sources, whatever it restored, and rebuilds whatever does not
match: reuse only changes how much there is to build, never what is
checked.

  lean_reuse.py select MANIFEST PLAN BASE
      Plan the build twice with `lean_shards.py plan`: against MANIFEST
      (main's last build, as before) and against the manifest of a build of
      the base commit (from the base commit's own `lean_shards.py
      manifest`). Reuse the base run when that saves at least MIN_SAVING s
      of module work and its outputs, and the build under them, are all
      still there. A merge queue entry whose base run is still building
      waits for it when the plan without it needs at least WAIT_FINISH s:
      the run ahead started first, so it finishes about when this one
      would have, and this one then builds only its own change (if the run
      ahead fails, the merge queue drops this entry anyway), for as long
      as the plan without it takes and WAIT_MARGIN more. Writes the
      chosen plan to PLAN (with `diagnostics.base` saying why), this run's
      `lean-base` to BASE (in the merge queue), and prints `count=`,
      `shards=`, `build-key=` and `base=` (a JSON list of the runs to
      reuse, in order, or nothing) for $GITHUB_OUTPUT. Reads GH_REPO,
      GH_TOKEN (for `gh`), EVENT (the event's name), MATCHED (the key of
      MANIFEST's cache) and GITHUB_RUN_ID.
  lean_reuse.py fetch RUNS DIR
      Download the `lean-build-*` artifacts of each run of RUNS (`base=`)
      into DIR/<nn>-<run>/, `nn` its place in RUNS.
  lean_reuse.py extract DIR BUILD [--modules FILE | --except FILE]
      Extract the outputs fetched into DIR over BUILD (`lean/.lake/build`),
      run by run, in order, and in each run its shards' before its
      assembly's; with --modules, only the outputs of the modules FILE
      lists (`lean_shards.py closure`) and those of no module of the
      project; with --except, only the others.
"""

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time

import lean_shards

CI = pathlib.Path(__file__).resolve().parent
ROOT = CI.parent
# Module work (s) the base run must save: fetching its outputs costs every
# job that builds about half a minute.
MIN_SAVING = 300.0
# How long the plan without the base run must take (its estimate, s) for a
# merge queue entry to wait for its base run. A shorter build waiting would
# finish later than it would have alone.
WAIT_FINISH = 1200.0
# How long to wait for a base run at most: as long as the build without it
# would take, and some, but never past the merge queue's patience.
WAIT_MARGIN = 600.0
WAIT_LIMIT = 60 * 60.0
POLL = 30
# The most runs a run reuses: a longer chain is a queue of long builds,
# which main's next saved build ends.
MAX_CHAIN = 8
FINAL = "lean-build-final-"
QUEUE = "gh-readonly-queue/main/"


def log(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, stdout=subprocess.PIPE, text=True).stdout


class GitHub:
    """What `select` asks GitHub, through `gh`."""

    def __init__(self, repo: str):
        self.repo = repo

    def queue_runs(self, sha: str) -> list[dict]:
        """The merge queue's runs of the workflow on `sha`."""
        out = gh("api", f"repos/{self.repo}/actions/workflows/ci.yml/runs"
                 f"?head_sha={sha}&event=merge_group&per_page=100")
        return json.loads(out)["workflow_runs"]

    def artifacts(self, run: int) -> set[str]:
        """The names of the unexpired artifacts of `run`."""
        out = gh("api", "--paginate", f"repos/{self.repo}/actions/runs/{run}/artifacts?per_page=100",
                 "--jq", ".artifacts[] | select(.expired | not) | .name")
        return set(out.split())

    def completed(self, run: int) -> bool:
        return gh("api", f"repos/{self.repo}/actions/runs/{run}", "--jq", ".status").strip() == "completed"

    def cache_exists(self, key: str) -> bool:
        # `key` matches by prefix: look for the key itself.
        out = gh("api", "--paginate", f"repos/{self.repo}/actions/caches?key={key}&per_page=100",
                 "--jq", ".actions_caches[].key")
        return key in out.split()

    def base_of(self, run: int, directory: pathlib.Path) -> dict:
        gh("run", "download", str(run), "-R", self.repo, "-n", "lean-base", "-D", str(directory))
        return json.loads((directory / "lean-base.json").read_text())

    def download(self, run: int, directory: pathlib.Path) -> None:
        for attempt in range(3):
            shutil.rmtree(directory, ignore_errors=True)
            try:
                gh("run", "download", str(run), "-R", self.repo, "-p", "lean-build-*", "-D", str(directory))
                return
            except subprocess.CalledProcessError:
                if attempt == 2:
                    raise
                log(f"Downloading run {run}'s outputs failed: trying again.")
                time.sleep(10)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, cwd=ROOT, stdout=subprocess.PIPE, text=True).stdout


def base_commit(event: str) -> str | None:
    """The commit whose merge queue run a run of `event` reuses."""
    rev = "HEAD" if event == "push" else "HEAD^1"
    try:
        return git("rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}").strip()
    except subprocess.CalledProcessError:
        return None


def base_manifest(commit: str, manifest: str, out: pathlib.Path) -> bool:
    """Write to `out` the manifest a build of `commit` would save, with
    `manifest`'s times for the modules it has not changed: `commit`'s own
    `lean_shards.py manifest`, on its own sources."""
    tree = out.parent / "base-tree"
    tree.mkdir()
    archive = subprocess.Popen(["git", "archive", commit, "ci", "lean"], cwd=ROOT, stdout=subprocess.PIPE)
    unpack = subprocess.run(["tar", "-x", "-C", str(tree)], stdin=archive.stdout)
    archive.stdout.close()
    if archive.wait() or unpack.returncode:
        return False
    with out.open("w") as f:
        made = subprocess.run([sys.executable, str(tree / "ci" / "lean_shards.py"), "manifest",
                               str(pathlib.Path(manifest).resolve())], stdout=f)
    return made.returncode == 0


def plan(manifest: str, out: pathlib.Path) -> tuple[dict, dict[str, str]]:
    """`lean_shards.py plan`'s plan, and what it prints for $GITHUB_OUTPUT."""
    made = subprocess.run([sys.executable, str(CI / "lean_shards.py"), "plan", manifest, str(out)],
                          check=True, stdout=subprocess.PIPE, text=True)
    outputs = dict(line.split("=", 1) for line in made.stdout.splitlines() if "=" in line)
    return json.loads(out.read_text()), outputs


def finish(p: dict) -> float:
    return p.get("diagnostics", {}).get("selected", {}).get("finish_s", 0.0)


def built(names: set[str]) -> bool:
    """Whether a run's artifacts hold the outputs of its whole build."""
    return any(n.startswith(FINAL) for n in names)


def ready(names: set[str]) -> bool:
    """Whether a run's artifacts are those of a whole build to reuse."""
    return "lean-base" in names and built(names)


def queue_run(runs: list[dict], own: int) -> dict | None:
    """The newest of the merge queue's runs of a commit, but this one."""
    runs = [r for r in runs if r["head_branch"].startswith(QUEUE) and r["id"] != own]
    return max(runs, key=lambda r: r["id"]) if runs else None


def build_key(manifest_key: str) -> str | None:
    """The key of the build saved with the manifest of key `manifest_key`."""
    prefix = "lean-manifest-"
    return "lean-build-" + manifest_key[len(prefix):] if manifest_key.startswith(prefix) else None


def chain_of(base: dict, run: int) -> tuple[str, list[int]] | None:
    """The build of main and the runs to reuse to rebuild `run`'s build,
    from its `lean-base`; None if it is not one."""
    key, runs = base.get("manifest_key"), base.get("runs")
    if (not isinstance(key, str) or build_key(key) is None or not isinstance(runs, list)
            or not all(isinstance(r, int) and not isinstance(r, bool) for r in runs)):
        return None
    return key, [*runs, run]


def wait(github, run: int, limit: float = WAIT_LIMIT, poll: float = POLL,
         clock=time.monotonic, sleep=time.sleep) -> bool:
    """Wait for the outputs of `run`'s whole build: whether they came."""
    deadline = clock() + limit
    while True:
        if ready(github.artifacts(run)):
            return True
        # Its last upload may come just before it completes.
        if github.completed(run):
            return ready(github.artifacts(run))
        if clock() >= deadline:
            return False
        sleep(poll)


def select(event, manifest, matched, plan_path, base_path, github, own, work, *,
           commit_of=base_commit, manifest_of=base_manifest, plan_of=plan,
           wait_for=wait, clock=time.monotonic):
    """The chosen plan's outputs for $GITHUB_OUTPUT (see the module's
    documentation); writes the plan to `plan_path` and, in the merge
    queue, this run's `lean-base` to `base_path`."""
    p0, out0 = plan_of(manifest, work / "plan-main.json")
    chosen, outputs, chain, key = p0, out0, [], matched
    report = {"used": False, "work_without": p0["work"], "finish_without_s": finish(p0)}

    def decide():
        # Most runs: nothing to save, so no second plan (seconds) to make.
        if p0["work"] < MIN_SAVING:
            return "saves too little"
        commit = commit_of(event)
        if commit is None:
            return "no base commit"
        report["commit"] = commit
        b = queue_run(github.queue_runs(commit), own)
        if b is None:
            return "no merge queue run of the base commit"
        report["run"] = run = b["id"]
        whole = ready(github.artifacts(run))
        if not whole:
            if b["status"] == "completed":
                return "the base run has no whole build"
            if event != "merge_group" or finish(p0) < WAIT_FINISH:
                return "the base run is still building, and waiting does not pay"
        if not manifest_of(commit, manifest, work / "manifest-base.json"):
            return "could not write the base commit's manifest"
        p1, out1 = plan_of(str(work / "manifest-base.json"), work / "plan-base.json")
        report["work_with"], report["finish_with_s"] = p1["work"], finish(p1)
        if p0["work"] - p1["work"] < MIN_SAVING:
            return "saves too little"
        if not whole:
            log(f"Waiting for run {run}, which builds the base commit {commit}.")
            started = clock()
            came = wait_for(github, run, min(WAIT_LIMIT, finish(p0) + WAIT_MARGIN))
            report["waited_s"] = round(clock() - started)
            if not came:
                return "the base run's build did not come"
        c = chain_of(github.base_of(run, work / "base"), run)
        if c is None:
            return "the base run's lean-base is invalid"
        bottom, runs = c
        if len(runs) > MAX_CHAIN:
            return "the chain of base runs is too long"
        if not all(built(github.artifacts(r)) for r in runs[:-1]):
            return "a reused run's outputs are gone"
        if not github.cache_exists(build_key(bottom)):
            return "the build the base run built on is gone"
        nonlocal chosen, outputs, chain, key
        chosen, outputs, chain, key = p1, out1, runs, bottom
        report["used"] = True
        return "reused"

    try:
        report["reason"] = decide()
    except (subprocess.CalledProcessError, OSError, ValueError, KeyError) as e:
        # Never fail the build over it: plan it as before.
        report["reason"] = f"failed: {e!r}"
    log(f"Base run: {report['reason']} ({json.dumps(report)}).")
    # As lean_shards.py states a plan, last: what ci_metrics.py reads.
    log(f"{chosen['stale']} modules to build, about {chosen['work']} s; "
        f"shards' estimated times: {chosen['loads']}")
    if key and build_key(key):
        log(f"The plan builds on {build_key(key)}.")
    chosen.setdefault("diagnostics", {})["base"] = report
    pathlib.Path(plan_path).write_text(json.dumps(chosen, indent=1) + "\n")
    if event == "merge_group" and key:
        pathlib.Path(base_path).write_text(json.dumps({"manifest_key": key, "runs": chain}) + "\n")
    lines = [f"count={outputs['count']}", f"shards={outputs['shards']}"]
    if key and build_key(key):
        lines.append(f"build-key={build_key(key)}")
    lines.append(f"base={json.dumps(chain) if chain else ''}")
    return lines


def tarballs(run_dir: pathlib.Path) -> list[pathlib.Path]:
    """A run's outputs, its shards' before its assembly's."""
    return sorted(run_dir.rglob("*.tar.zst"), key=lambda p: (p.name.startswith(FINAL), p.name))


def kept(path: str, modules: set[str], mode: str | None) -> bool:
    if mode is None:
        return True
    m = lean_shards.module_of_output(path)
    if mode == "except":
        return m not in modules
    project = any(m == lib or m.startswith(f"{lib}.") for lib in lean_shards.LIBRARIES)
    return m in modules or not project


def extract(directory: pathlib.Path, build: pathlib.Path, modules: set[str] = frozenset(),
            mode: str | None = None) -> int:
    """Extract the fetched outputs (see the module's documentation); the
    number of files."""
    build.mkdir(parents=True, exist_ok=True)
    count = 0
    for run_dir in sorted(d for d in directory.iterdir() if d.is_dir()):
        for tarball in tarballs(run_dir):
            # GNU tar recognises the compression when reading a file.
            listed = subprocess.run(["tar", "-tf", str(tarball)], check=True,
                                    stdout=subprocess.PIPE, text=True).stdout.splitlines()
            names = [n for n in listed if not n.endswith("/") and kept(n, modules, mode)]
            if not names:
                continue
            count += len(names)
            if mode is None:
                subprocess.run(["tar", "-xf", str(tarball), "-C", str(build)], check=True)
                continue
            with tempfile.NamedTemporaryFile("w", delete=False) as f:
                f.write("\0".join(names) + "\0")
            try:
                subprocess.run(["tar", "-xf", str(tarball), "-C", str(build), "--null", "--no-wildcards",
                                "--verbatim-files-from", "-T", f.name], check=True)
            finally:
                os.unlink(f.name)
    return count


def main(args: list[str]) -> int:
    if len(args) == 4 and args[0] == "select":
        with tempfile.TemporaryDirectory() as work:
            lines = select(os.environ["EVENT"], args[1], os.environ.get("MATCHED", ""), args[2], args[3],
                           GitHub(os.environ["GH_REPO"]), int(os.environ.get("GITHUB_RUN_ID", "0")),
                           pathlib.Path(work))
        print("\n".join(lines))
        return 0
    if len(args) == 3 and args[0] == "fetch":
        github = GitHub(os.environ["GH_REPO"])
        directory = pathlib.Path(args[2])
        for i, run in enumerate(json.loads(args[1])):
            log(f"Downloading the Lean outputs of run {run}.")
            github.download(run, directory / f"{i:02d}-{run}")
        return 0
    if len(args) in (3, 5) and args[0] == "extract":
        mode, modules = None, set()
        if len(args) == 5:
            if args[3] not in ("--modules", "--except"):
                print(__doc__, file=sys.stderr)
                return 2
            mode = args[3][2:]
            modules = set(pathlib.Path(args[4]).read_text().split())
        n = extract(pathlib.Path(args[1]), pathlib.Path(args[2]), modules, mode)
        log(f"Extracted {n} files of the reused runs' outputs.")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
