"""How `lean_closure.py` attributes and scores imports; no builds."""

import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest import mock

import lean_closure as closure
import lean_shards as shards


class Dominators(unittest.TestCase):
    # S imports A and B; both import C; only A imports D.
    imps = {"S": ["A", "B"], "A": ["C", "D"], "B": ["C"], "C": [], "D": []}
    cost = {"S": 1.0, "A": 2.0, "B": 3.0, "C": 4.0, "D": 5.0}

    def test_a_module_two_imports_share_is_neither_s(self):
        dom = closure.dominators(self.imps, "S", self.cost)
        self.assertEqual(dom["C"], (4.0, 1, "S"))
        self.assertEqual(dom["D"], (5.0, 1, "A"))
        # A's subtree: A and D, not C, which B imports too.
        self.assertEqual(dom["A"], (7.0, 2, "S"))
        self.assertEqual(dom["S"], (15.0, 5, None))

    def test_a_chain(self):
        dom = closure.dominators({"S": ["A"], "A": ["B"], "B": []}, "S", {"S": 1.0, "A": 1.0, "B": 1.0})
        self.assertEqual(dom["A"], (2.0, 2, "S"))
        self.assertEqual(dom["B"], (1.0, 1, "A"))


class FirstBuilt(unittest.TestCase):
    def test_the_modules_whose_imports_were_not_rebuilt(self):
        imps = {"S": ["A"], "A": ["B"], "B": [], "C": []}
        self.assertEqual(closure.first_built(imps, {"S", "A", "C"}), {"A", "C"})

    def test_modules_no_longer_there(self):
        self.assertEqual(closure.first_built({"A": []}, {"A", "Gone"}), {"A"})


def hub(name: str, n: int) -> dict[str, list[str]]:
    """A module `name` importing `n` modules of its own."""
    parts = [f"{name}{i}" for i in range(n)]
    return {name: parts, **{p: [] for p in parts}}


class Score(unittest.TestCase):
    # Three sinks, each importing a hub of 20 modules; X imports Y's too, so
    # a plan builds Y's hub twice or packs X and Y in one shard.
    base = {**hub("A", 20), **hub("B", 20), **hub("C", 20), "X": ["A", "B"], "Y": ["B"], "Z": ["C"]}
    times = dict.fromkeys(base, 300.0)
    new = {**base, "X": ["A"]}

    def test_dropping_a_shared_import(self):
        [(name, b, n)] = closure.score(self.base, self.new, self.times, [])
        self.assertEqual(name, "full")
        self.assertEqual((b["shards"], b["twice"]), (2, 6300.0))
        self.assertEqual((n["shards"], n["twice"]), (3, 0.0))
        self.assertLess(n["slowest"], b["slowest"])
        self.assertLessEqual(n["slowest_at"], b["slowest"])

    def test_a_run_rebuilds_what_imports_what_it_changed(self):
        # The run changed B3, and so rebuilt the hub B, X and Y.
        built = {"B3": 300.0, "B": 300.0, "X": 300.0, "Y": 300.0}
        [_, (name, b, n)] = closure.score(self.base, self.new, self.times, [("7", built)])
        self.assertEqual(name, "7")
        self.assertEqual((b["stale"], n["stale"]), (4, 3))

    def test_unchanged_imports_change_nothing(self):
        built = {"A1": 300.0, "A": 300.0, "X": 300.0}
        for _, b, n in closure.score(self.base, self.base, self.times, [("7", built)]):
            self.assertEqual(b, n)


class Metrics(unittest.TestCase):
    def test_runs_and_times(self):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            run = lambda built: {"lean": {"jobs": [{"built": {"step": built}}]}}
            (d / "2.json").write_text(json.dumps(run({"A": 2.0})))
            (d / "10.json").write_text(json.dumps(run({"A": 10.0, "B": 1.0})))
            (d / "3.json").write_text(json.dumps(run({})))
            (d / "profile.json").write_text(json.dumps({"C": 1.0}))
            runs = closure.load_runs(d)
            # Oldest first, by run number; a run that built nothing is left out.
            self.assertEqual([r for r, _ in runs], ["2", "10"])
            times = closure.latest_times(runs, {"A": 0.5, "C": 1.0})
            self.assertEqual(times, {"A": 10.0, "B": 1.0, "C": 1.0 + closure.IMPORT_TIME})


class ImportsAt(unittest.TestCase):
    def test_the_modules_and_imports_of_a_revision(self):
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            files = {
                "lean/VerifiedGarbage.lean": "import VerifiedGarbage.A\n",
                "lean/VerifiedGarbage/A.lean": "import VerifiedGarbage.B\nimport Mathlib.Tactic.Ring\n",
                "lean/VerifiedGarbage/B.lean": "",
                "lean/VerifiedGarbageTest/T.lean": "import VerifiedGarbage.B\n",
                "lean/Emit.lean": "import VerifiedGarbage\n",
            }
            for f, text in files.items():
                (root / f).parent.mkdir(parents=True, exist_ok=True)
                (root / f).write_text(text)
            git = lambda *a: subprocess.run(["git", "-C", d, *a], check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "c")
            (root / "lean/VerifiedGarbage/B.lean").write_text("import VerifiedGarbage.A\n")
            with mock.patch.object(closure, "ROOT", root):
                self.assertEqual(closure.imports_at("HEAD"), {
                    "VerifiedGarbage": ["VerifiedGarbage.A"],
                    "VerifiedGarbage.A": ["VerifiedGarbage.B"],
                    "VerifiedGarbage.B": [],
                    "VerifiedGarbageTest.T": ["VerifiedGarbage.B"],
                })


class Schedule(unittest.TestCase):
    def test_plan_is_schedule_of_the_stale_modules(self):
        imps = {"A": [], "B": ["A"]}
        work, path, (loads, targets, built) = shards.schedule(imps, shards.closures(imps), {"B"}, {"A": 5.0, "B": 7.0})
        self.assertEqual(work, 7.0 + 0)  # A is up to date
        self.assertAlmostEqual(path["B"], 7.0 + shards.UP_TO_DATE)
        self.assertEqual((loads, targets, built), ([], [], []))


if __name__ == "__main__":
    unittest.main()
