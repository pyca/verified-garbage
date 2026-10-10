"""What the Lean build's plan counts as changed; no builds."""

import pathlib
import tempfile
import unittest
from unittest import mock

import lean_shards as shards

LAKEFILE = """name = "VerifiedGarbage"
moreLeanArgs = ["-j2"]

[[lean_lib]]
name = "VerifiedGarbage"
globs = ["VerifiedGarbage.*"]

# Compiled specifications.
[[lean_lib]]
name = "NativeSpec"
roots = []
globs = ["VerifiedGarbage.Spec.A"]
precompileModules = true
"""


class LakefileInputs(unittest.TestCase):
    def test_comments_and_layout_change_nothing(self):
        other = LAKEFILE.replace("# Compiled specifications.\n", "").replace(
            'globs = ["VerifiedGarbage.Spec.A"]', 'globs = [\n  "VerifiedGarbage.Spec.A",\n]')
        self.assertEqual(shards.lakefile_inputs(other), shards.lakefile_inputs(LAKEFILE))

    def test_module_lists_are_not_settings(self):
        settings, libraries = shards.lakefile_inputs(LAKEFILE)
        added = LAKEFILE.replace('"VerifiedGarbage.Spec.A"]', '"VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        settings2, libraries2 = shards.lakefile_inputs(added)
        self.assertEqual(settings2, settings)
        self.assertEqual(libraries["NativeSpec"], ["globs:VerifiedGarbage.Spec.A"])
        self.assertEqual(libraries2["NativeSpec"], ["globs:VerifiedGarbage.Spec.A", "globs:VerifiedGarbage.Spec.B"])

    def test_settings(self):
        settings = shards.lakefile_inputs(LAKEFILE)[0]
        for old, new in [
            ('moreLeanArgs = ["-j2"]', 'moreLeanArgs = ["-j4"]'),
            ("precompileModules = true", "precompileModules = false"),
            ('name = "NativeSpec"', 'name = "NativeSpecs"'),
        ]:
            with self.subTest(new=new):
                self.assertNotEqual(shards.lakefile_inputs(LAKEFILE.replace(old, new))[0], settings)


class Matches(unittest.TestCase):
    closure = {"A": frozenset({"A", "B"})}

    def test_entries(self):
        for entry, module, expected in [
            ("globs:X.*", "X", True),
            ("globs:X.*", "X.Y.Z", True),
            ("globs:X.*", "XY", False),
            ("globs:X.+", "X", False),
            ("globs:X.+", "X.Y", True),
            ("globs:X.Y", "X.Y", True),
            ("globs:X.Y", "X.Y.Z", False),
            ("roots:A", "B", True),
            ("roots:A", "C", False),
            ("roots:C", "C", True),
        ]:
            with self.subTest(entry=entry, module=module):
                self.assertEqual(shards.matches(entry, module, self.closure), expected)


class Project(unittest.TestCase):
    """A small project, and the manifest of its build."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.lean = pathlib.Path(tmp.name)
        patch = mock.patch.object(shards, "LEAN", self.lean)
        patch.start()
        self.addCleanup(patch.stop)
        for name, text in {
            "lean-toolchain": "leanprover/lean4:v4.34.1\n",
            "lake-manifest.json": "{}\n",
            "lakefile.toml": LAKEFILE,
            "VerifiedGarbage.lean": "import VerifiedGarbage.Proof\n",
            "VerifiedGarbage/Spec/A.lean": "\n",
            "VerifiedGarbage/Spec/B.lean": "\n",
            "VerifiedGarbage/Proof.lean": "import VerifiedGarbage.Spec.A\nimport VerifiedGarbage.Spec.B\n",
            "VerifiedGarbage/Other.lean": "\n",
        }.items():
            (self.lean / name).parent.mkdir(parents=True, exist_ok=True)
            (self.lean / name).write_text(text)
        self.manifest = {
            "inputs": shards.inputs(),
            "sources": {m: shards.digest(f) for m, f in shards.modules().items()},
        }


class Plan(Project):
    """`plan` on the small project, against the manifest of its build."""

    def stale(self):
        return shards.plan(self.manifest)["stale"]

    def edit(self, old, new):
        f = self.lean / "lakefile.toml"
        f.write_text(f.read_text().replace(old, new))

    def test_unchanged(self):
        self.assertEqual(self.stale(), 0)

    def test_adding_a_module_to_a_library(self):
        # Spec.B moves to NativeSpec: it, and what imports it, rebuild.
        self.edit('"VerifiedGarbage.Spec.A"]', '"VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        self.assertEqual(self.stale(), 3)

    def test_a_comment(self):
        self.edit("# Compiled specifications.", "# The compiled specifications.")
        self.assertEqual(self.stale(), 0)

    def test_a_setting_rebuilds_everything(self):
        self.edit('moreLeanArgs = ["-j2"]', 'moreLeanArgs = ["-j4"]')
        self.assertEqual(self.stale(), 5)

    def test_toolchain_rebuilds_everything(self):
        (self.lean / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        self.assertEqual(self.stale(), 5)

    def test_an_older_manifest_rebuilds_everything(self):
        self.manifest["inputs"] = {f: shards.digest(self.lean / f) for f in shards.INPUTS}
        self.assertEqual(self.stale(), 5)

    @mock.patch.object(shards, "SHARD_OVERHEAD", 0.0)
    def test_shard_count(self):
        # Every module is stale; the work is 5 times each module's time. The
        # project has two sinks: a third shard would have nothing to build.
        self.manifest["inputs"] = {}
        for each, count in [(50, 0), (160, 0), (161, 2), (300, 2), (330, 2), (4000, 2)]:
            with self.subTest(work=5 * each):
                self.manifest["times"] = {m: each for m in self.manifest["sources"]}
                self.assertEqual(len(shards.plan(self.manifest)["targets"]), count)

    def test_no_shards_when_a_chain_sets_the_time(self):
        # The root module's chain of three imports takes 12000 s however the
        # work is split: shards would only add their overhead.
        self.manifest["inputs"] = {}
        self.manifest["times"] = {m: 4000 for m in self.manifest["sources"]}
        self.assertEqual(shards.plan(self.manifest)["targets"], [])


class WallTime(unittest.TestCase):
    # D imports B and C, which import A.
    imps = {"A": [], "B": ["A"], "C": ["A"], "D": ["B", "C"]}

    def test_critical_path(self):
        cost = {"A": 10.0, "B": 20.0, "C": 5.0, "D": 10.0}
        self.assertEqual(shards.paths(self.imps, cost), {"A": 10.0, "B": 30.0, "C": 15.0, "D": 40.0})
        self.assertEqual(shards.wall_time(self.imps, cost), 40.0)

    def test_only_the_modules_built(self):
        # B is not built: D's chain is through C.
        cost = {"A": 10.0, "C": 5.0, "D": 10.0}
        self.assertEqual(shards.wall_time(self.imps, cost), 25.0)

    def test_throughput(self):
        imps = {str(i): [] for i in range(10)}
        cost = {m: 10.0 for m in imps}
        self.assertEqual(shards.wall_time(imps, cost), 100.0 / shards.PARALLELISM)
        self.assertEqual(shards.wall_time({}, {}), 0.0)


@mock.patch.object(shards, "SHARD_OVERHEAD", 0.0)
class Chain(Project):
    """`plan` with a long chain of imports and many short modules (which the
    `lean` job would build as fast without shards' overhead)."""

    CHAIN = [f"VerifiedGarbage.Chain{i}" for i in range(3)]
    SHORT = [f"VerifiedGarbage.Short{i}" for i in range(20)]

    def setUp(self):
        super().setUp()
        for i, m in enumerate(self.CHAIN):
            text = f"import {self.CHAIN[i - 1]}\n" if i else "\n"
            (self.lean / f"{m.replace('.', '/')}.lean").write_text(text)
        for m in self.SHORT:
            (self.lean / f"{m.replace('.', '/')}.lean").write_text("\n")
        self.manifest["inputs"] = {}
        self.manifest["times"] = {m: 1.0 for m in shards.modules()}
        self.manifest["times"].update({m: 100.0 for m in self.CHAIN})
        self.manifest["times"].update({m: 30.0 for m in self.SHORT})

    def test_the_chain_takes_no_other_work(self):
        # Balancing the work alone would give the chain's shard a quarter of
        # the short modules (each shard about 450 s of work); but the chain
        # takes 300 s however many modules the runner builds at once, and
        # the other shard builds all the short ones in less.
        p = shards.plan(self.manifest)
        self.assertEqual(len(p["targets"]), 2)
        chain = p["owner"][self.CHAIN[-1]]
        self.assertEqual(p["targets"][chain], [self.CHAIN[-1]])
        self.assertLessEqual(set(self.SHORT), set(p["targets"][1 - chain]))
        self.assertEqual(p["loads"][chain], 300)
        # The plan's estimates are the shards' wall times.
        imps = shards.imports(shards.modules())
        closure = shards.closures(imps)
        for targets, load in zip(p["targets"], p["loads"]):
            built = set().union(*(closure[t] for t in targets))
            self.assertEqual(load, round(shards.wall_time(imps, {m: self.manifest["times"][m] for m in built})))


class Many(Project):
    """`plan` with many modules that nothing imports, of equal times."""

    SINKS = [f"VerifiedGarbage.Sink{i}" for i in range(40)]

    def setUp(self):
        super().setUp()
        for m in self.SINKS:
            (self.lean / f"{m.replace('.', '/')}.lean").write_text("\n")
        self.manifest["inputs"] = {}

    def count(self, each):
        self.manifest["times"] = {m: (each if m in self.SINKS else 0.0) for m in shards.modules()}
        return len(shards.plan(self.manifest)["targets"])

    def test_a_shard_per_work(self):
        # 2000 s of work: three shards (two would be slower).
        self.assertEqual(self.count(50), 3)

    def test_no_shard_that_is_no_faster(self):
        # 16000 s of work would take `MAX_SHARDS`; but each sink takes 400 s
        # however many a runner builds at once, as long as 5 or fewer: 8
        # shards are as fast.
        self.assertEqual(self.count(400), 8)

    def test_no_shards_that_save_less_than_their_overhead(self):
        # 880 s of work: two shards would take 81 s each, the `lean` job
        # 163 s, less than their 81 s and `SHARD_OVERHEAD`.
        self.assertEqual(self.count(22), 0)
        # 1000 s: 93 s each, against 185 s.
        self.assertEqual(self.count(25), 2)


class Prune(Project):
    """`prune` on the build of the small project, after a module is gone."""

    KEPT = [
        "lib/lean/VerifiedGarbage.olean",
        "lib/lean/VerifiedGarbage/Spec/A.olean",
        "lib/lean/VerifiedGarbage/Spec/A.olean.hash",
        "ir/VerifiedGarbage/Spec/A.c",
        "ir/VerifiedGarbage/Spec/A.c.o.export",
        # Outputs of no module of the libraries.
        "lib/libVerifiedGarbage_NativeSpec.so",
        "ir/Emit.c",
        "bin/emit",
    ]
    DELETED = [
        "lib/lean/VerifiedGarbage/Old.olean",
        "lib/lean/VerifiedGarbage/Old.trace",
        "lib/lean/VerifiedGarbage/Gone/X.ilean",
        "ir/VerifiedGarbage/Gone/X.c",
        "lib/lean/VerifiedGarbageTest/Old.olean",
    ]

    def test_deletes_the_outputs_of_deleted_modules(self):
        build = self.lean / ".lake" / "build"
        for name in self.KEPT + self.DELETED:
            (build / name).parent.mkdir(parents=True, exist_ok=True)
            (build / name).write_text("")
        self.assertEqual(shards.main(["prune", str(build)]), 0)
        left = sorted(f.relative_to(build).as_posix() for f in build.rglob("*") if f.is_file())
        self.assertEqual(left, sorted(self.KEPT))
        self.assertFalse((build / "lib/lean/VerifiedGarbage/Gone").exists())
        self.assertFalse((build / "lib/lean/VerifiedGarbageTest").exists())


if __name__ == "__main__":
    unittest.main()
