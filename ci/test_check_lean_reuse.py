"""How a run chooses to build on the merge queue's run of its base commit,
and extracts that run's outputs; no builds, and GitHub faked."""

import contextlib
import io
import json
import pathlib
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest import mock

import lean_reuse as reuse

MAIN = "lean-manifest-Linux-X64-abc-111"
BOTTOM = "lean-manifest-Linux-X64-abc-000"


def plan(work, finish, count=0):
    return ({"stale": int(work), "work": work, "loads": [finish] * count, "targets": [],
             "diagnostics": {"selected": {"shards": count, "finish_s": finish}}},
            {"count": str(count), "shards": json.dumps([str(i + 1) for i in range(count)])})


class FakeGitHub:
    def __init__(self, runs=None, artifacts=None, base=None, caches=(BOTTOM.replace("manifest", "build"),),
                 completed=True):
        self.runs = runs if runs is not None else [
            {"id": 7, "head_branch": "gh-readonly-queue/main/pr-1-aaa", "status": "completed"}]
        self.arts = artifacts if artifacts is not None else {7: {"lean-base", "lean-build-1", "lean-build-final-2"}}
        self.base = base if base is not None else {"manifest_key": BOTTOM, "runs": []}
        self.caches = set(caches)
        self.done = completed

    def queue_runs(self, sha):
        return self.runs

    def artifacts(self, run):
        return self.arts.get(run, set())

    def completed(self, run):
        return self.done

    def cache_exists(self, key):
        return key in self.caches

    def base_of(self, run, directory):
        return self.base


class Select(unittest.TestCase):
    def run_select(self, github, event="merge_group", p0=plan(60000, 1500, 12), p1=plan(40, 15), waited=None):
        self.tmp = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        plans = {"plan-main.json": p0, "plan-base.json": p1}
        calls = []

        def wait_for(gh, run, limit):
            calls.append((run, limit))
            return waited

        with contextlib.redirect_stderr(io.StringIO()) as err:
            lines = reuse.select(
                event, "manifest.json", MAIN, self.tmp / "plan.json", self.tmp / "base.json", github, 99,
                self.tmp, commit_of=lambda e: "c0ffee", manifest_of=lambda c, m, out: True,
                plan_of=lambda m, out: plans[out.name], wait_for=wait_for)
        self.log = err.getvalue()
        self.waits = calls
        out = dict(line.split("=", 1) for line in lines)
        chosen = json.loads((self.tmp / "plan.json").read_text())
        base = (json.loads((self.tmp / "base.json").read_text())
                if (self.tmp / "base.json").exists() else None)
        return out, chosen, base

    def test_reuses_the_base_run(self):
        out, chosen, base = self.run_select(FakeGitHub())
        self.assertEqual(out, {"count": "0", "shards": "[]", "build-key": "lean-build-Linux-X64-abc-000",
                               "base": "[7]"})
        self.assertEqual(chosen["work"], 40)
        self.assertEqual(chosen["diagnostics"]["base"]["reason"], "reused")
        self.assertEqual(base, {"manifest_key": BOTTOM, "runs": [7]})
        self.assertIn("40 modules to build, about 40 s; shards' estimated times: []", self.log.splitlines()[-2])
        self.assertIn("The plan builds on lean-build-Linux-X64-abc-000.", self.log)

    def test_follows_the_base_runs_chain(self):
        github = FakeGitHub(base={"manifest_key": BOTTOM, "runs": [3, 5]},
                            artifacts={3: {"lean-build-final-1"}, 5: {"lean-build-final-lean"},
                                       7: {"lean-base", "lean-build-final-lean"}})
        out, _, base = self.run_select(github)
        self.assertEqual(out["base"], "[3, 5, 7]")
        self.assertEqual(base["runs"], [3, 5, 7])

    def test_a_small_saving_plans_against_main(self):
        out, chosen, base = self.run_select(FakeGitHub(), p0=plan(300, 100), p1=plan(100, 30))
        self.assertEqual(out, {"count": "0", "shards": "[]", "build-key": "lean-build-Linux-X64-abc-111",
                               "base": ""})
        self.assertEqual(chosen["work"], 300)
        self.assertEqual(chosen["diagnostics"]["base"]["reason"], "saves too little")
        self.assertEqual(base, {"manifest_key": MAIN, "runs": []})

    def test_a_small_build_asks_nothing(self):
        github = FakeGitHub()
        github.queue_runs = github.artifacts = mock.Mock(side_effect=AssertionError("asked"))
        out, chosen, _ = self.run_select(github, p0=plan(200, 50))
        self.assertEqual(out["base"], "")
        self.assertEqual(chosen["diagnostics"]["base"]["reason"], "saves too little")

    def test_only_the_merge_queue_writes_its_base(self):
        _, _, base = self.run_select(FakeGitHub(), event="pull_request")
        self.assertIsNone(base)
        _, _, base = self.run_select(FakeGitHub(), event="push")
        self.assertIsNone(base)

    def test_waits_in_the_merge_queue_for_a_long_build(self):
        github = FakeGitHub(artifacts={7: {"lean-base"}})
        github.runs[0]["status"] = "in_progress"
        out, chosen, _ = self.run_select(github, waited=True)
        self.assertEqual(self.waits, [(7, 1500 + reuse.WAIT_MARGIN)])
        self.assertEqual(out["base"], "[7]")
        self.assertIn("waited_s", chosen["diagnostics"]["base"])

    def test_gives_up_when_the_build_does_not_come(self):
        github = FakeGitHub(artifacts={7: set()})
        github.runs[0]["status"] = "in_progress"
        out, chosen, _ = self.run_select(github, waited=False)
        self.assertEqual(out["base"], "")
        self.assertEqual(chosen["work"], 60000)

    def test_never_waits_outside_the_merge_queue_or_for_a_short_build(self):
        for event, p0 in (("pull_request", plan(60000, 1500, 12)), ("merge_group", plan(6000, 600, 4))):
            github = FakeGitHub(artifacts={7: {"lean-base"}})
            github.runs[0]["status"] = "in_progress"
            out, chosen, _ = self.run_select(github, event=event, p0=p0)
            self.assertEqual(self.waits, [])
            self.assertEqual(out["base"], "")
            self.assertEqual(chosen["work"], p0[0]["work"])

    def test_a_completed_run_without_a_whole_build_is_not_reused(self):
        out, _, _ = self.run_select(FakeGitHub(artifacts={7: {"lean-base", "lean-build-1"}}))
        self.assertEqual(out["base"], "")

    def test_refusals(self):
        cases = {
            "no merge queue run of the base commit": FakeGitHub(runs=[
                {"id": 7, "head_branch": "feature", "status": "completed"},
                {"id": 99, "head_branch": "gh-readonly-queue/main/pr-2-b", "status": "in_progress"}]),
            "the base run's lean-base is invalid": FakeGitHub(base={"manifest_key": "other", "runs": []}),
            "the chain of base runs is too long": FakeGitHub(
                base={"manifest_key": BOTTOM, "runs": list(range(20, 20 + reuse.MAX_CHAIN))}),
            "a reused run's outputs are gone": FakeGitHub(base={"manifest_key": BOTTOM, "runs": [3]}),
            "the build the base run built on is gone": FakeGitHub(caches=()),
        }
        for reason, github in cases.items():
            with self.subTest(reason):
                out, chosen, _ = self.run_select(github)
                self.assertEqual(chosen["diagnostics"]["base"]["reason"], reason)
                self.assertEqual(out["base"], "")
                self.assertEqual(out["build-key"], "lean-build-Linux-X64-abc-111")

    def test_errors_plan_against_main(self):
        github = FakeGitHub()
        github.queue_runs = mock.Mock(side_effect=subprocess.CalledProcessError(1, ["gh"]))
        out, chosen, _ = self.run_select(github)
        self.assertEqual(out["base"], "")
        self.assertTrue(chosen["diagnostics"]["base"]["reason"].startswith("failed: "))


class Helpers(unittest.TestCase):
    def test_queue_run(self):
        runs = [{"id": 5, "head_branch": "gh-readonly-queue/main/pr-1-a"},
                {"id": 9, "head_branch": "gh-readonly-queue/main/pr-1-a"},
                {"id": 12, "head_branch": "gh-readonly-queue/main/pr-1-a"},
                {"id": 30, "head_branch": "main"}]
        self.assertEqual(reuse.queue_run(runs, 12)["id"], 9)
        self.assertIsNone(reuse.queue_run(runs[3:], 12))

    def test_chain_of(self):
        self.assertEqual(reuse.chain_of({"manifest_key": BOTTOM, "runs": [1, 2]}, 3), (BOTTOM, [1, 2, 3]))
        for bad in ({}, {"manifest_key": BOTTOM}, {"manifest_key": BOTTOM, "runs": [True]},
                    {"manifest_key": BOTTOM, "runs": ["1"]}, {"manifest_key": 1, "runs": []}):
            self.assertIsNone(reuse.chain_of(bad, 3))

    def test_wait(self):
        now = [0.0]
        github = FakeGitHub(artifacts={7: set()}, completed=False)

        def sleep(s):
            now[0] += s
            if now[0] >= 60:
                github.arts[7] = {"lean-base", "lean-build-final-3"}

        self.assertTrue(reuse.wait(github, 7, limit=600, poll=30, clock=lambda: now[0], sleep=sleep))
        self.assertEqual(now[0], 60)
        github = FakeGitHub(artifacts={7: set()}, completed=False)
        now[0] = 0.0
        self.assertFalse(reuse.wait(github, 7, limit=90, poll=30, clock=lambda: now[0],
                                    sleep=lambda s: now.__setitem__(0, now[0] + s)))
        github = FakeGitHub(artifacts={7: {"lean-base"}}, completed=True)
        self.assertFalse(reuse.wait(github, 7, clock=lambda: 0.0, sleep=self.fail))


def add_tar(path: pathlib.Path, files: dict[str, str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(path, "w") as tar:
        for name, text in files.items():
            data = text.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))


class Extract(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        fetched = self.tmp / "fetched"
        # Run 3's assembly rebuilt B after its shard; run 5 then rebuilt A.
        add_tar(fetched / "00-3" / "lean-build-final-1" / "lean-build-final-1.tar.zst",
                {"lib/lean/VerifiedGarbage/B.olean": "B@3-final"})
        add_tar(fetched / "00-3" / "lean-build-1" / "lean-build-1.tar.zst",
                {"lib/lean/VerifiedGarbage/A.olean": "A@3", "lib/lean/VerifiedGarbage/B.olean": "B@3",
                 "lib/lean/libNative.so": "native@3"})
        add_tar(fetched / "01-5" / "lean-build-2" / "lean-build-2.tar.zst",
                {"lib/lean/VerifiedGarbage/A.olean": "A@5", "ir/VerifiedGarbage/A.c": "A.c@5"})
        self.fetched = fetched

    def read(self, build):
        return {p.relative_to(build).as_posix(): p.read_text() for p in sorted(build.rglob("*")) if p.is_file()}

    def test_later_runs_and_assemblies_win(self):
        build = self.tmp / "build"
        self.assertEqual(reuse.extract(self.fetched, build), 6)
        self.assertEqual(self.read(build), {
            "ir/VerifiedGarbage/A.c": "A.c@5", "lib/lean/VerifiedGarbage/A.olean": "A@5",
            "lib/lean/VerifiedGarbage/B.olean": "B@3-final", "lib/lean/libNative.so": "native@3"})

    def test_modules_and_the_rest(self):
        some, rest = self.tmp / "some", self.tmp / "rest"
        reuse.extract(self.fetched, some, {"VerifiedGarbage.A"}, "modules")
        self.assertEqual(self.read(some), {
            "ir/VerifiedGarbage/A.c": "A.c@5", "lib/lean/VerifiedGarbage/A.olean": "A@5",
            "lib/lean/libNative.so": "native@3"})
        reuse.extract(self.fetched, rest, {"VerifiedGarbage.A"}, "except")
        self.assertEqual(self.read(rest), {
            "lib/lean/VerifiedGarbage/B.olean": "B@3-final", "lib/lean/libNative.so": "native@3"})

    def test_main(self):
        modules = self.tmp / "modules"
        modules.write_text("VerifiedGarbage.B\n")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(reuse.main(["extract", str(self.fetched), str(self.tmp / "b"),
                                         "--modules", str(modules)]), 0)
            self.assertEqual(reuse.main(["extract", str(self.fetched), str(self.tmp / "b"),
                                         "--only", str(modules)]), 2)
        self.assertEqual(set(self.read(self.tmp / "b")),
                         {"lib/lean/VerifiedGarbage/B.olean", "lib/lean/libNative.so"})


class BaseManifest(unittest.TestCase):
    """The base commit's manifest, from its own sources and planner."""

    def test_base_manifest(self):
        tmp = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        repo = tmp / "repo"
        (repo / "ci").mkdir(parents=True)
        shutil.copy(reuse.CI / "lean_shards.py", repo / "ci")
        lean = repo / "lean"
        (lean / "VerifiedGarbage").mkdir(parents=True)
        (lean / "lakefile.toml").write_text('name = "VerifiedGarbage"\n\n[[lean_lib]]\nname = "VerifiedGarbage"\n')
        (lean / "lean-toolchain").write_text("leanprover/lean4:v4.0.0\n")
        (lean / "lake-manifest.json").write_text("{}\n")
        (lean / "VerifiedGarbage" / "A.lean").write_text("-- A\n")

        def git(*args):
            subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=repo,
                           check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

        git("init", "-q")
        git("add", ".")
        git("commit", "-qm", "base")
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                                stdout=subprocess.PIPE, text=True).stdout.strip()
        # Changed after the commit: the manifest is of the commit's sources.
        (lean / "VerifiedGarbage" / "B.lean").write_text("-- B\n")
        (tmp / "work").mkdir()
        (tmp / "other").mkdir()
        out = tmp / "work" / "manifest.json"
        with mock.patch.object(reuse, "ROOT", repo), contextlib.redirect_stderr(io.StringIO()):
            self.assertTrue(reuse.base_manifest(commit, str(tmp / "missing.json"), out))
            # No such commit.
            self.assertFalse(reuse.base_manifest("0" * 40, str(tmp / "missing.json"), tmp / "other" / "m.json"))
        manifest = json.loads(out.read_text())
        self.assertEqual(list(manifest["sources"]), ["VerifiedGarbage.A"])
        self.assertEqual(manifest["times"], {})


if __name__ == "__main__":
    unittest.main()
