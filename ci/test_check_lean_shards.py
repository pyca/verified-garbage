"""What the Lean build's plan counts as changed; no builds."""

import contextlib
import hashlib
import io
import json
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
platformIndependent = true

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

    def test_generated_library_is_not_a_setting(self):
        # Adding the emitter's generated library, or changing its settings,
        # rebuilds no other module; its module lists are kept.
        settings = shards.lakefile_inputs(LAKEFILE)[0]
        lib = '\n[[lean_lib]]\nname = "VGEmit"\nsrcDir = ".lake/emit/src"\nglobs = ["VGEmit.+"]\n'
        for added in (LAKEFILE + lib, LAKEFILE + lib + "platformIndependent = true\n"):
            with self.subTest(added=added):
                settings2, libraries2 = shards.lakefile_inputs(added)
                self.assertEqual(settings2, settings)
                self.assertEqual(libraries2["VGEmit"], ["globs:VGEmit.+"])

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


class SourceInfo(Project):
    def test_literal_search_matches_full_regex_scanning(self):
        import random
        rng = random.Random(51)
        fragments = ["public", "meta", "import", "all", "A", "B", "Unknown",
                     "-- import A", "important", "metadata", "def x := 1", "/-", "-/"]
        spaces = [" ", "\t", "\n", "\n\n", "\u2003"]
        mods = {"A", "B", "public", "meta", "import"}
        for _ in range(300):
            text = "".join(rng.choice(fragments) + rng.choice(spaces) for _ in range(40))
            expected = [(bool(p), bool(a), i) for p, a, i in shards.IMPORT_KIND.findall(text) if i in mods]
            self.assertEqual(shards.import_kinds(text, mods), expected)
        text = 'def x := "' + "import public meta " * 1000 + '"\nimport A\n'
        self.assertEqual(shards.import_kinds(text, mods), [(False, False, "A")])

    def test_parse_normalized_newlines_but_hash_original_bytes(self):
        raw = ("module\r\n\r\n\tpublic meta import all VerifiedGarbage.Spec.B\r\n"
               "import VerifiedGarbage.Other\r\n-- π\r\n").encode("utf-8")
        path = self.lean / "VerifiedGarbage/Spec/A.lean"
        path.write_bytes(raw)
        imps, vis, hashes = shards.source_info(shards.modules())
        name = "VerifiedGarbage.Spec.A"
        self.assertEqual(imps[name], ["VerifiedGarbage.Spec.B", "VerifiedGarbage.Other"])
        self.assertEqual(vis[name], (["VerifiedGarbage.Spec.B"], ["VerifiedGarbage.Spec.B"]))
        self.assertEqual(hashes[name], hashlib.sha256(raw).hexdigest())

    def test_legacy_sources_and_multiline_imports(self):
        path = self.lean / "VerifiedGarbage/Spec/A.lean"
        path.write_bytes(b"\r\tpublic\rmeta import all\rVerifiedGarbage.Spec.B\r")
        imps, vis, _ = shards.source_info(shards.modules())
        self.assertEqual(imps["VerifiedGarbage.Spec.A"], ["VerifiedGarbage.Spec.B"])
        self.assertIsNone(vis["VerifiedGarbage.Spec.A"])


class Diagnostics(Project):
    def test_cli_retains_inputs_and_still_produces_a_usable_plan(self):
        self.manifest["times"] = {"VerifiedGarbage.Spec.A": 17.5}
        (self.lean / "VerifiedGarbage/Spec/B.lean").write_text("-- edited\n")
        manifest = self.lean / "manifest.json"
        manifest.write_text(json.dumps(self.manifest))
        dest = self.lean / "plan.json"
        expected = shards.plan(self.manifest)
        env = {"GITHUB_RUN_ID": "7", "GITHUB_RUN_ATTEMPT": "2"}
        with mock.patch.dict(shards.os.environ, env), contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(shards.main(["plan", str(manifest), str(dest)]), 0)
        actual = json.loads(dest.read_text())
        d = actual.pop("diagnostics")
        self.assertEqual(actual, expected)
        self.assertEqual(d["historical_times"], self.manifest["times"])
        self.assertEqual(d["inputs"], shards.inputs())
        self.assertEqual((d["run_id"], d["run_attempt"]), ("7", "2"))
        self.assertEqual(d["settings"]["parallelism"], shards.PARALLELISM)
        self.assertEqual(len(d["stale_modules"]), actual["stale"])
        self.assertEqual(d["timed_stale_modules"], 0)
        self.assertEqual(d["fallback_time_s"], 17.5)
        self.assertEqual(d["planner_sha256"], shards.digest(pathlib.Path(shards.__file__)))
        self.assertGreaterEqual(d["planning_s"], 0)

    def test_unchanged_keeps_the_fast_path_and_records_no_work(self):
        d = {}
        with mock.patch.object(shards, "closures", side_effect=AssertionError("unnecessary graph")):
            p = shards.plan(self.manifest, d)
        self.assertEqual(p["stale"], 0)
        self.assertEqual(d["stale_modules"], [])
        self.assertEqual(d["selected"]["finish_s"], 0)

    def test_diagnostics_do_not_change_shard_selection_and_cover_duplicate_assignments(self):
        imps = {"shared": [], **{str(i): ["shared"] for i in range(20)}}
        closure = shards.closures(imps)
        times = {"shared": 5.0, **dict.fromkeys(map(str, range(20)), 100.0)}
        expected = shards.schedule(imps, closure, set(imps), times)
        d = {}
        actual = shards.schedule(imps, closure, set(imps), times, d)
        self.assertEqual(actual, expected)
        loads, targets, built = actual[2]
        self.assertGreater(len(targets), 1)
        self.assertEqual(d["assignments"], [sorted(part) for part in built])
        self.assertEqual(d["selected"]["finish_s"], max(loads) + shards.SHARD_OVERHEAD)
        work = sum(times[m] for part in built for m in part)
        self.assertAlmostEqual(d["selected"]["duplicate_work_s"], work - sum(times.values()))
        self.assertEqual(d["timed_stale_modules"], len(imps))
        self.assertEqual(d["candidates"][0]["shards"], 0)
        self.assertEqual({c["shards"] for c in d["candidates"]}, {0, *range(2, shards.MAX_SHARDS + 1)})





class MetaDependencies(unittest.TestCase):
    def test_import_modes_do_not_upgrade_a_private_meta_import_to_public(self):
        modes = {}
        text = "module\npublic import B\nmeta import B\npublic meta import C\nmeta import all D\n"
        kinds = shards.import_kinds(text, {"B", "C", "D"}, modes)
        self.assertEqual(kinds, [(True, False, "B"), (False, False, "B"),
                                 (True, False, "C"), (False, True, "D")])
        self.assertEqual(modes, {"meta": ["B", "C", "D"], "public_meta": ["C"]})

    def test_meta_reads_private_transitive_inputs_and_public_meta_passes_them_on(self):
        imps = {"C": [], "B": ["C"], "Plain": ["B"], "Meta": ["B"],
                "Export": ["B"], "Downstream": ["Export"],
                "Mixed": ["B"], "MixedDownstream": ["Mixed"]}
        vis = dict.fromkeys(imps, ([], []))
        vis["Export"] = (["B"], [])
        vis["Mixed"] = (["B"], [])
        modes = {"Meta": {"meta": ["B"]},
                 "Export": {"meta": ["B"], "public_meta": ["B"]},
                 "Mixed": {"meta": ["B"]}}
        closure = shards.closures(imps)
        self.assertEqual(shards.stale_of({"C"}, shards.reads(imps, closure, vis)), {"C", "B"})
        self.assertEqual(shards.stale_of({"C"}, shards.reads(imps, closure, vis, modes)),
                         {"C", "B", "Meta", "Export", "Downstream", "Mixed"})

    def test_import_all_includes_meta_inputs_of_private_imports(self):
        imps = {"C": [], "B": ["C"], "Bridge": ["B"], "All": ["Bridge"]}
        vis = dict.fromkeys(imps, ([], []))
        vis["All"] = ([], ["Bridge"])
        modes = {"Bridge": {"meta": ["B"]}}
        read = shards.reads(imps, shards.closures(imps), vis, modes)
        self.assertIn("C", read["All"])

    def test_among_intersects_every_trace(self):
        # Public, private, meta and `all` imports, and a file that is not a module.
        imps = {"C": [], "D": [], "B": ["C", "D"], "Pub": ["B"], "Priv": ["Pub"],
                "Meta": ["B"], "All": ["Priv"], "File": ["Priv"]}
        vis = dict.fromkeys(imps, ([], []))
        vis["Pub"] = (["B"], [])
        vis["All"] = ([], ["Priv"])
        vis["File"] = None
        modes = {"Meta": {"meta": ["B"]}}
        closure = shards.closures(imps)
        read = shards.reads(imps, closure, vis, modes)
        for among in (frozenset({"C"}), frozenset({"B", "D"}), frozenset({"Pub", "Priv"})):
            self.assertEqual(shards.closures(imps, among), {m: c & among for m, c in closure.items()})
            self.assertEqual(shards.reads(imps, shards.closures(imps, among), vis, modes, among),
                             {m: r & among for m, r in read.items()})


class NativeRequirements(Project):
    def test_scoped_targets_remain_module_targets(self):
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps({"targets": [["VerifiedGarbage.Proof"]]}))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(shards.main(["targets", str(plan), "1"]), 0)
        self.assertEqual(out.getvalue().splitlines(), ["+VerifiedGarbage.Proof"])

    def test_trace_settings_keep_ordinary_proofs_independent(self):
        closure = shards.closures(shards.imports(shards.modules()))
        self.assertEqual(shards.native_trace_modules(closure), {"VerifiedGarbage.Spec.A"})

    def test_unrelated_native_member_invalidates_private_transitive_importers(self):
        imps = {"A": [], "B": [], "Consumer": ["A"], "Downstream": ["Consumer"]}
        closure = shards.closures(imps)
        libraries = {"Native": frozenset({"A", "B"})}
        ordinary = shards.reads(imps, closure, dict.fromkeys(imps, ([], [])))
        native = shards.native_reads(imps, closure, libraries)
        combined = {m: ordinary[m] | native[m] for m in imps}
        self.assertEqual(shards.stale_of({"B"}, ordinary), {"B"})
        self.assertEqual(shards.stale_of({"B"}, combined), {"B", "Consumer", "Downstream"})
        self.assertNotIn("B", native["A"])

    def test_members_of_one_native_library_do_not_read_unrelated_siblings(self):
        imps = {"Helper": [], "Main": ["Helper"], "Unrelated": []}
        closure = shards.closures(imps)
        native = shards.native_reads(imps, closure, {"Native": frozenset(imps)})
        self.assertEqual(native["Main"], frozenset({"Helper"}))
        self.assertEqual(native["Unrelated"], frozenset())

    def test_transitive_native_libraries_are_import_closed(self):
        imps = {"A": [], "B": ["C"], "C": [], "D": [], "Sink": ["A"]}
        closure = shards.closures(imps)
        libraries = {"One": frozenset({"A", "B"}), "Two": frozenset({"C", "D"})}
        required = shards.build_requirements(closure, libraries)
        self.assertEqual(required["Sink"], frozenset(imps))
        self.assertEqual(required["D"], frozenset({"C", "D"}))
        for part in required.values():
            for m in part:
                self.assertLessEqual(closure[m], part)

    def test_schedule_counts_native_members_absent_from_normal_imports(self):
        imps = {"A": [], "B": [], **{f"Sink{i}": ["A"] for i in range(20)}}
        closure = shards.closures(imps)
        required = shards.build_requirements(closure, {"Native": frozenset({"A", "B"})})
        times = {"A": 1., "B": 100., **{f"Sink{i}": 500. for i in range(20)}}
        d = {}
        _, _, (_, targets, built) = shards.schedule(imps, closure, set(imps), times, d,
                                                    requirements=required)
        self.assertTrue(targets)
        for ts, part in zip(targets, built):
            self.assertEqual(part, set().union(*(required[t] for t in ts)))
        self.assertLessEqual(set(imps), set().union(*built))
        total = sum(times[m] for part in built for m in part)
        self.assertEqual(d["selected"]["module_work_s"], total)
        self.assertAlmostEqual(d["selected"]["duplicate_work_s"], total - sum(times.values()))


class TimingHistory(unittest.TestCase):
    def setUp(self):
        self.sources = {"M": "source", "N": "unchanged"}
        self.inputs = {"toolchain": "v1"}
        self.old = {"inputs": self.inputs, "sources": self.sources,
                    "times": {"M": 100.0, "N": 10.0}}

    def update(self, observations, old=None, sources=None, inputs=None):
        return shards.update_timings(old or self.old, observations,
                                     sources or self.sources, inputs or self.inputs)

    def test_duplicate_shards_are_combined_without_file_order_bias(self):
        samples = [{"version": 1, "components": {"M": {"lean": t}}} for t in (10, 1000, 12)]
        left = self.update(samples)
        self.assertEqual(left, self.update(list(reversed(samples))))
        self.assertEqual(left[0], {"M": 12, "N": 10})
        self.assertEqual(left[1]["M"]["lean"], [12])

    def test_partial_final_assembly_cannot_replace_module_time(self):
        samples = [
            {"version": 1, "components": {"M": {"lean": 20, "c.o": 5}}},
            {"version": 1, "components": {"M": {"dynlib": 1}}},
        ]
        times, history = self.update(samples)
        self.assertEqual(times["M"], 26)
        old = dict(self.old, times=times, timing_history=history)
        times, _ = self.update([{ "version": 1, "components": {"M": {"dynlib": 3}}}], old)
        self.assertEqual(times["M"], 27)

    def test_recent_same_source_samples_resist_outliers_and_adapt(self):
        old = self.old
        for sample, expected in [(10, 10), (12, 11), (1000, 12), (14, 14), (16, 16)]:
            times, history = self.update([{"M": sample}], old)
            self.assertEqual(times["M"], expected)
            self.assertLessEqual(len(history["M"]["total"]), 3)
            old = dict(self.old, times=times, timing_history=history)

    def test_changed_source_or_toolchain_drops_unmeasured_old_timings(self):
        times, history = self.update([], sources={"M": "new", "N": "unchanged"})
        self.assertEqual(times, {"N": 10})
        self.assertEqual(history, {})
        times, history = self.update([], inputs={"toolchain": "v2"})
        self.assertEqual((times, history), ({}, {}))

    def test_changed_source_starts_new_history(self):
        old = dict(self.old, timing_history={"M": {"lean": [100, 120, 140]}})
        times, history = self.update([{"version": 1, "components": {"M": {"lean": 5}}}],
                                     old, sources={"M": "new", "N": "unchanged"})
        self.assertEqual(times["M"], 5)
        self.assertEqual(history["M"], {"lean": [5]})

    def test_moving_library_members_resets_only_affected_timings(self):
        inputs = dict(self.inputs, libraries={"Native": ["roots:M"]})
        closure = {"M": frozenset({"M"}), "N": frozenset({"N"})}
        times, history = shards.update_timings(self.old, [], self.sources, inputs, closure)
        self.assertEqual(times, {"N": 10})
        self.assertEqual(history, {})

    def test_native_only_sample_preserves_unsplittable_legacy_total(self):
        times, history = self.update([{"version": 1, "components": {"M": {"c.o": 2}}}])
        self.assertEqual(times["M"], 100)
        self.assertEqual(history["M"], {"c.o": [2]})

    def test_deleted_modules_and_invalid_measurements(self):
        times, _ = self.update([{"gone": 200}], sources={"N": "unchanged"})
        self.assertEqual(times, {"N": 10})
        for value in (-1, float("nan"), float("inf")):
            with self.assertRaises(ValueError):
                self.update([{"M": value}])

    def test_log_components_do_not_confuse_linking_with_compilation(self):
        parsed = shards.log_timings(Times.LOG)
        self.assertEqual(parsed["components"]["VerifiedGarbage.Proof.Framework.Omega"],
                         {"lean": 1.2, "c.o": 8.8, "dynlib": .15})
        self.assertNotIn("NativeTactics", parsed["components"])


class TimingEstimates(unittest.TestCase):
    def test_unknown_uses_size_matched_peers_in_nearest_namespace(self):
        peers = {f"VG.Proof.Family.M{i}": float(i + 1) for i in range(8)}
        unrelated = {f"VG.Spec.M{i}": 100.0 for i in range(8)}
        other_sizes = {f"VG.Proof.Family.Large{i}": 200.0 for i in range(8)}
        unknown = "VG.Proof.Family.New"
        times = peers | unrelated | other_sizes
        sizes = dict.fromkeys(peers | unrelated, 1024) | dict.fromkeys(other_sizes, 8192) | {unknown: 1500}
        estimates, _ = shards.timing_estimates(dict.fromkeys([*times, unknown]), times, sizes)
        self.assertEqual(estimates[unknown], 6.0)
        self.assertEqual(estimates["VG.Spec.M0"], 100.0)

    def test_sparse_or_legacy_inputs_keep_global_fallback(self):
        times = {"A": 1.0, "B": 4.0, "C": 9.0}
        for sizes in (None, {"A": 100, "new": 100}):
            estimates, default = shards.timing_estimates(dict.fromkeys([*times, "new"]), times, sizes)
            self.assertEqual(estimates["new"], 4.0)
            self.assertEqual(default, 4.0)
        estimates, _ = shards.timing_estimates({"new": []}, {}, {"new": 0})
        self.assertEqual(estimates["new"], shards.DEFAULT_TIME)

    def test_unknown_chain_costs_are_included_and_retained(self):
        peers = {f"VG.Proof.M{i}": [] for i in range(8)}
        imps = peers | {"VG.Proof.New": ["VG.Proof.M0"], "VG.Proof.End": ["VG.Proof.New"]}
        times = dict.fromkeys(peers, 100.0)
        sizes = dict.fromkeys(imps, 1024)
        diagnostics = {}
        work, _, _ = shards.schedule(imps, shards.closures(imps), set(imps), times,
                                      diagnostics, source_bytes=sizes)
        self.assertEqual(work, 1000.0)
        self.assertEqual(diagnostics["fallback_estimates"],
                         {"VG.Proof.End": 100.0, "VG.Proof.New": 100.0})


class Plan(Project):
    """`plan` on the small project, against the manifest of its build."""

    def stale(self):
        return shards.plan(self.manifest)["stale"]

    def edit(self, old, new):
        f = self.lean / "lakefile.toml"
        f.write_text(f.read_text().replace(old, new))

    def test_unchanged(self):
        self.assertEqual(self.stale(), 0)

    def test_unchanged_does_not_construct_closures(self):
        with mock.patch.object(shards, "closures", side_effect=AssertionError("unnecessary graph")):
            self.assertEqual(shards.plan(self.manifest),
                             {"stale": 0, "work": 0, "loads": [], "targets": [], "owner": {}, "edited": []})

    def test_adding_a_module_to_a_library(self):
        # Spec.B moves to NativeSpec: it, and what imports it, rebuild.
        self.edit('"VerifiedGarbage.Spec.A"]', '"VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        self.assertEqual(self.stale(), 3)

    def test_a_comment(self):
        self.edit("# Compiled specifications.", "# The compiled specifications.")
        self.assertEqual(self.stale(), 0)

    def test_a_module_s_imports(self):
        # Proof as a module: a change to Spec.A still rebuilds it and its importer.
        (self.lean / "VerifiedGarbage/Proof.lean").write_text(
            "module\n\npublic import VerifiedGarbage.Spec.A\nmeta import VerifiedGarbage.Spec.B\n")
        self.manifest["sources"] = {m: shards.digest(f) for m, f in shards.modules().items()}
        (self.lean / "VerifiedGarbage/Spec/A.lean").write_text("-- changed\n")
        self.assertEqual(self.stale(), 3)

    def change_spec_a(self, files):
        """The modules to rebuild when Spec.A changes, with `files` written
        over the project and the manifest taken after them."""
        for name, text in files.items():
            (self.lean / name).write_text(text)
        self.manifest["sources"] = {m: shards.digest(f) for m, f in shards.modules().items()}
        (self.lean / "VerifiedGarbage/Spec/A.lean").write_text("module\n-- changed\n")
        mods = shards.modules()
        imps = shards.imports(mods)
        read = shards.reads(imps, shards.closures(imps), shards.visibilities(mods))
        return sorted(shards.stale_of({"VerifiedGarbage.Spec.A"}, read))

    def test_a_private_import_stops_the_rebuild(self):
        # Proof imports Spec.A privately: Proof rebuilds, but Other, which
        # imports Proof, reads nothing of Spec.A.
        self.assertEqual(self.change_spec_a({
            "VerifiedGarbage/Proof.lean": "module\n\nimport VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\npublic import VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "module\n\nimport VerifiedGarbage.Other\n",
        }), ["VerifiedGarbage.Proof", "VerifiedGarbage.Spec.A"])

    def test_a_public_import_passes_it_on(self):
        self.assertEqual(self.change_spec_a({
            "VerifiedGarbage/Proof.lean": "module\n\npublic import VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\nimport VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "module\n\nimport VerifiedGarbage.Other\n",
        }), ["VerifiedGarbage.Other", "VerifiedGarbage.Proof", "VerifiedGarbage.Spec.A"])

    def test_meta_imports_are_imports(self):
        self.assertEqual(self.change_spec_a({
            "VerifiedGarbage/Proof.lean": "module\n\npublic meta import VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\nmeta import VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "module\n\nimport VerifiedGarbage.Other\n",
        }), ["VerifiedGarbage.Other", "VerifiedGarbage.Proof", "VerifiedGarbage.Spec.A"])

    def test_import_all_reads_private_imports(self):
        # `import all Proof` reads what Proof imports, privately or not.
        self.assertEqual(self.change_spec_a({
            "VerifiedGarbage/Proof.lean": "module\n\nimport VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\nimport all VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "module\n\nimport VerifiedGarbage.Other\n",
        }), ["VerifiedGarbage.Other", "VerifiedGarbage.Proof", "VerifiedGarbage.Spec.A"])

    def test_a_file_that_is_not_a_module_reads_everything(self):
        # The root, not a module, reads the whole closure; Other, a module
        # importing Proof (which imports Spec.A privately), reads nothing of it.
        self.assertEqual(self.change_spec_a({
            "VerifiedGarbage/Proof.lean": "module\n\nimport VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\npublic import VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "import VerifiedGarbage.Other\n",
        }), ["VerifiedGarbage", "VerifiedGarbage.Proof", "VerifiedGarbage.Spec.A"])

    def test_the_plan_counts_only_what_reads_the_change(self):
        for name, text in {
            "VerifiedGarbage/Proof.lean": "module\n\nimport VerifiedGarbage.Spec.A\n",
            "VerifiedGarbage/Other.lean": "module\n\npublic import VerifiedGarbage.Proof\n",
            "VerifiedGarbage.lean": "module\n\nimport VerifiedGarbage.Other\n",
        }.items():
            (self.lean / name).write_text(text)
        self.manifest["sources"] = {m: shards.digest(f) for m, f in shards.modules().items()}
        (self.lean / "VerifiedGarbage/Spec/A.lean").write_text("module\n-- changed\n")
        self.assertEqual(self.stale(), 2)

    def test_the_edited_modules(self):
        # Listed whatever the inputs: a toolchain change rebuilds everything,
        # but only Spec.A's source changed.
        (self.lean / "VerifiedGarbage/Spec/A.lean").write_text("-- changed\n")
        (self.lean / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        p = shards.plan(self.manifest)
        self.assertEqual(p["edited"], ["VerifiedGarbage.Spec.A"])
        self.assertNotIn("edited", shards.plan({}))

    def test_needed_takes_whole_precompiled_libraries(self):
        self.edit('globs = ["VerifiedGarbage.Spec.A"]', 'globs = ["VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        (self.lean / "VerifiedGarbage/UsesA.lean").write_text("import VerifiedGarbage.Spec.A\n")
        closure = shards.closures(shards.imports(shards.modules()))
        # Importing Spec.A loads NativeSpec, built from Spec.B too.
        self.assertEqual(shards.needed(["VerifiedGarbage.UsesA"], closure),
                         {"VerifiedGarbage.UsesA", "VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"})
        self.assertEqual(shards.needed(["VerifiedGarbage.Other"], closure), {"VerifiedGarbage.Other"})

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
    def test_no_shard_count_can_shorten_the_dependency_chain(self):
        # Every module is stale, but a dependency chain sets the time and
        # the independent module fits alongside it. Splitting cannot help,
        # even with no shard overhead and arbitrarily large module times.
        self.manifest["inputs"] = {}
        for each in [50, 160, 161, 300, 330, 4000]:
            with self.subTest(work=5 * each):
                self.manifest["times"] = {m: each for m in self.manifest["sources"]}
                self.assertEqual(shards.plan(self.manifest)["targets"], [])

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
        # Six modules share the effective 5.4 slots, then four run at full
        # speed: the last wave cannot fill the runner.
        self.assertAlmostEqual(shards.wall_time(imps, cost), 60.0 / shards.PARALLELISM + 10)
        self.assertEqual(shards.wall_time({}, {}), 0.0)

    def test_parallel_work_between_serial_barriers(self):
        imps = {"root": [], **{f"p{i}": ["root"] for i in range(12)},
                "end": [f"p{i}" for i in range(12)]}
        cost = dict.fromkeys(imps, 100.0)
        # The lower bound is only 300 s. The serial prefix and suffix
        # cannot overlap either wave of the parallel work.
        self.assertAlmostEqual(shards.build_time(imps, cost), 200 + 1200 / shards.PARALLELISM)

    def test_input_order_does_not_change_scheduling(self):
        imps = {"root": [], **{f"p{i}": ["root"] for i in range(20)},
                "end": [f"p{i}" for i in range(20)]}
        cost = {m: float(i + 1) for i, m in enumerate(imps)}
        reversed_imps = {m: list(reversed(imps[m])) for m in reversed(imps)}
        self.assertEqual(shards.build_time(imps, cost),
                         shards.build_time(reversed_imps, dict(reversed(list(cost.items())))))

    def test_reused_graph_matches_standalone_simulation_of_closed_subsets(self):
        import random
        rng = random.Random(12)
        imps = {str(i): [str(j) for j in range(i) if rng.random() < .15] for i in range(50)}
        closure = shards.closures(imps)
        cost = {m: rng.choice([0.0, .02, 1.0, 3.5, 20.0]) for m in imps}
        graph = shards._BuildGraph(imps, cost)
        for _ in range(30):
            targets = rng.sample(sorted(imps), rng.randrange(1, 6))
            modules = set().union(*(closure[t] for t in targets))
            self.assertEqual(graph.time(modules), shards.build_time(imps, {m: cost[m] for m in modules}))

    def test_cached_simulations_respect_parallelism(self):
        imps = {str(i): [] for i in range(4)}
        graph = shards._BuildGraph(imps, dict.fromkeys(imps, 10.0))
        modules = set(imps)
        self.assertEqual(graph.time(modules), 10.0)
        self.assertEqual(graph.time(modules), 10.0)
        with mock.patch.object(shards, "PARALLELISM", 1.0):
            self.assertEqual(graph.time(modules), 40.0)
        self.assertEqual(graph.time(modules), 10.0)


class RebuildFrontier(unittest.TestCase):
    @mock.patch.object(shards, "PARALLELISM", 2.0)
    @mock.patch.object(shards, "SHARD_OVERHEAD", 95.0)
    def test_solo_participates_in_the_latency_tolerance(self):
        imps = {str(i): [] for i in range(4)}
        # Solo: 200 s; two shards: 100 + 95 s. The five-second
        # improvement is within 5%, so avoid extra runners altogether.
        self.assertEqual(shards.schedule(imps, shards.closures(imps), set(imps),
                                         dict.fromkeys(imps, 100.0))[2], ([], [], []))

    def test_a_cached_module_between_two_stale_modules(self):
        imps = {"A": [], "B": ["A"], "C": ["B"], "D": ["A"]}
        closure = shards.closures(imps)
        self.assertEqual(shards.rebuild_targets({"A", "C", "D"}, closure), ["C", "D"])
        self.assertEqual(shards.rebuild_targets(set(), closure), [])

    def test_private_rebuilds_are_not_bundled_by_an_unchanged_importer(self):
        imps = {"unchanged": ["L", "R"]}
        for side in ["L", "R"]:
            imps[side] = [f"{side}{i}" for i in range(12)]
            imps.update({m: [] for m in imps[side]})
        # L and R import their leaves privately: changes to those leaves
        # rebuild L and R, while their importer stays cached.
        vis = dict.fromkeys(imps, ([], []))
        closure = shards.closures(imps)
        changed = {m for m in imps if not imps[m]}
        stale = shards.stale_of(changed, shards.reads(imps, closure, vis))
        self.assertNotIn("unchanged", stale)
        _, _, (loads, targets, built) = shards.schedule(imps, closure, stale, dict.fromkeys(imps, 100.0))
        self.assertEqual(len(loads), 2)
        self.assertEqual(sorted(t for ts in targets for t in ts), ["L", "R"])
        self.assertEqual(set.union(*built), stale)
        self.assertFalse(built[0] & built[1])

    def test_sharded_plans_cover_stale_modules_and_never_have_empty_targets(self):
        import random
        rng = random.Random(7)
        for _ in range(20):
            imps = {str(i): [str(j) for j in range(i) if rng.random() < .08] for i in range(40)}
            closure = shards.closures(imps)
            stale = {m for m in imps if rng.random() < .6}
            times = {m: rng.uniform(10, 400) for m in imps}
            _, _, (loads, targets, built) = shards.schedule(imps, closure, stale, times)
            if loads:
                self.assertTrue(all(targets))
                self.assertLessEqual(stale, set.union(*built))
                for ts, part in zip(targets, built):
                    self.assertLessEqual(set(ts), stale)
                    self.assertEqual(part, set().union(*(closure[t] for t in ts)))


class Packing(unittest.TestCase):
    @mock.patch.object(shards, "PARALLELISM", 1.0)
    def test_a_heavier_reuse_weight_keeps_a_sink_with_its_imports(self):
        # Four sinks import one base. Weighing the work a sink adds as time
        # alone, the last joins the idle shard and builds the base again;
        # weighing it twice, it joins the shard building the base already.
        imps = {"base": [], **{f"s{i}": ["base"] for i in range(4)}}
        closure = shards.closures(imps)
        cost = {"base": 100.0, **{f"s{i}": 50.0 for i in range(4)}}
        path = shards.paths(imps, cost)
        sinks = [f"s{i}" for i in range(4)]
        _, targets, built = shards.pack(2, sinks, closure, cost, path)
        self.assertEqual(targets, [["s0", "s1", "s2"], ["s3"]])
        self.assertIn("base", built[1])
        _, targets, built = shards.pack(2, sinks, closure, cost, path, reuse=2.0)
        self.assertEqual(targets, [sinks, []])

    def test_restored_modules_weigh_as_much_by_their_number(self):
        import math
        import random

        def summed(count, sinks, closure, cost, path, reuse):
            # Packing as it was, summing every module a sink adds.
            built, loads, longest = [set() for _ in range(count)], [0.0] * count, [0.0] * count
            targets = [[] for _ in range(count)]
            for s in sinks:
                added = [math.fsum(cost[m] for m in closure[s] - part) for part in built]
                best = min(range(count), key=lambda i: (
                    shards.estimate(loads[i] + added[i], max(longest[i], path[s]))
                    + reuse * added[i] / shards.PARALLELISM, i))
                built[best] |= closure[s]
                loads[best] += added[best]
                longest[best] = max(longest[best], path[s])
                targets[best].append(s)
            return targets, built

        rng = random.Random(3)
        for _ in range(10):
            imps = {str(i): [str(j) for j in range(i) if rng.random() < .1] for i in range(60)}
            closure = shards.closures(imps)
            cost = {m: rng.choice([shards.UP_TO_DATE, 1.0, 7.5, 40.0]) for m in imps}
            path = shards.paths(imps, cost)
            sinks = sorted(imps, key=lambda m: -sum(cost[x] for x in closure[m]))[:12]
            for reuse in shards.REUSE_WEIGHTS:
                _, targets, built = shards.pack(4, sinks, closure, cost, path, reuse)
                self.assertEqual((targets, built), summed(4, sinks, closure, cost, path, reuse))

    def test_worker_processes_pack_as_one_process_does(self):
        import random
        rng = random.Random(5)
        bases = [f"b{i}" for i in range(6)]
        imps = {**{b: [] for b in bases},
                **{str(i): rng.sample(bases, 2) for i in range(120)}}
        closure = shards.closures(imps)
        times = {m: rng.uniform(100, 300) for m in imps}
        with mock.patch.object(shards._Packings, "PARALLEL_SINKS", 10 ** 9):
            alone = shards.schedule(imps, closure, set(imps), times)
        with mock.patch.object(shards._Packings, "PARALLEL_SINKS", 0):
            together = shards.schedule(imps, closure, set(imps), times)
        self.assertEqual(alone, together)
        self.assertTrue(alone[2][1])

    @mock.patch.object(shards, "SHARD_OVERHEAD", 0.0)
    def test_every_weight_is_a_candidate_and_counts_outside_the_work_bound_are_not(self):
        imps = {"base": [], **{f"s{i}": ["base"] for i in range(30)}}
        times = {"base": 10.0, **{f"s{i}": 100.0 for i in range(30)}}
        d = {}
        shards.schedule(imps, shards.closures(imps), set(imps), times, d)
        packed = [c for c in d["candidates"] if "reuse" in c]
        self.assertEqual({c["reuse"] for c in packed}, set(shards.REUSE_WEIGHTS))
        bounded = [c["shards"] for c in d["candidates"] if c.get("excluded") == "work_bound"]
        self.assertTrue(bounded)
        self.assertFalse({c["shards"] for c in packed} & set(bounded))


class Refinement(unittest.TestCase):
    def example(self, imps, cost, targets, limit):
        closure = shards.closures(imps)
        built = [set().union(*(closure[t] for t in ts)) for ts in targets]
        loads = [shards.build_time(imps, {m: cost[m] for m in part}) for part in built]
        return shards.refine(imps, closure, cost, shards.paths(imps, cost), (loads, targets, built), limit)

    def test_reuses_shared_imports_without_exceeding_the_latency_budget(self):
        imps = {"shared": [], "A": ["shared"], "B": ["shared"], "C": []}
        cost = {"shared": 100.0, "A": 1.0, "B": 1.0, "C": 100.0}
        loads, targets, built = self.example(imps, cost, [["A"], ["B", "C"]], 101.0)
        self.assertEqual(targets, [["A", "B"], ["C"]])
        self.assertEqual(built, [{"shared", "A", "B"}, {"C"}])
        self.assertLessEqual(max(loads), 101.0)

    @mock.patch.object(shards, "PARALLELISM", 1.0)
    def test_does_not_save_work_by_exceeding_the_latency_budget(self):
        imps = {"shared": [], "A": ["shared"], "B": ["shared"], "C": []}
        cost = {"shared": 100.0, "A": 300.0, "B": 100.0, "C": 100.0}
        _, targets, _ = self.example(imps, cost, [["A"], ["B", "C"]], 400.0)
        self.assertEqual(targets, [["A"], ["B", "C"]])


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

    def test_solo_hides_independent_work_behind_the_chain(self):
        # Balancing the work alone would give the chain's shard a quarter of
        # the short modules (each shard about 450 s of work); but the chain
        # takes 300 s however many modules the runner builds at once, and
        # the other shard builds all the short ones in less.
        p = shards.plan(self.manifest)
        # The old planner chose two shards even though a single runner
        # could hide every short module behind the chain. Solo now takes
        # part in the same latency tolerance as the sharded candidates.
        self.assertEqual(p["targets"], [])


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

    @mock.patch.object(shards, "SHARD_OVERHEAD", 0.0)
    def test_only_sinks_with_something_to_build(self):
        # Half the sinks changed: the shards build those, and are given no
        # other sink (the root module, `Other`, the unchanged half).
        self.manifest["inputs"] = shards.inputs()
        self.manifest["sources"] = {m: shards.digest(f) for m, f in shards.modules().items()}
        self.manifest["times"] = {m: 400.0 for m in shards.modules()}
        changed = self.SINKS[:20]
        for m in changed:
            (self.lean / f"{m.replace('.', '/')}.lean").write_text("-- changed\n")
        p = shards.plan(self.manifest)
        self.assertGreater(len(p["targets"]), 1)
        self.assertEqual(sorted(t for ts in p["targets"] for t in ts), sorted(changed))
        # `closure`: what a shard needs of the last build, its sinks here.
        plan = self.lean / "plan.json"
        plan.write_text(json.dumps(p))
        with mock.patch("sys.stdout", new_callable=io.StringIO) as out:
            self.assertEqual(shards.main(["closure", str(plan), "1"]), 0)
        self.assertEqual(out.getvalue().split(), sorted(p["targets"][0]))

    @mock.patch.object(shards, "SHARD_OVERHEAD", 0.0)
    def test_new_modules(self):
        # Modules the last build lacks: a new sink, and a new module a
        # changed sink imports, which the closure of its shard holds.
        self.manifest["inputs"] = shards.inputs()
        self.manifest["sources"] = {m: shards.digest(f) for m, f in shards.modules().items()}
        self.manifest["times"] = {m: 400.0 for m in shards.modules()}
        changed = self.SINKS[:20]
        for m in changed:
            (self.lean / f"{m.replace('.', '/')}.lean").write_text("-- changed\n")
        (self.lean / "VerifiedGarbage/NewSink.lean").write_text("\n")
        (self.lean / "VerifiedGarbage/NewDep.lean").write_text("\n")
        (self.lean / "VerifiedGarbage/Sink0.lean").write_text("import VerifiedGarbage.NewDep\n")
        p = shards.plan(self.manifest)
        self.assertEqual(sorted(t for ts in p["targets"] for t in ts),
                         sorted(changed + ["VerifiedGarbage.NewSink"]))
        closure = shards.closures(shards.imports(shards.modules()))
        i = next(i for i, ts in enumerate(p["targets"]) if "VerifiedGarbage.Sink0" in ts)
        self.assertIn("VerifiedGarbage.NewDep", shards.needed(p["targets"][i], closure))

    def test_counts_are_not_capped_by_work(self):
        # 2000 s of independent work: the old work/800 cutoff allowed only
        # three shards. Seven finish close to eight, using fewer runners.
        self.assertEqual(self.count(50), 7)

    def test_uncompetitive_counts_are_not_simulated(self):
        imps = {str(i): [] for i in range(40)}
        simulate = shards._BuildGraph.time
        parts = []

        def record(graph, modules=None):
            if modules is not None:
                parts.append(len(modules))
            return simulate(graph, modules)

        with mock.patch.object(shards._BuildGraph, "time", record):
            _, _, (_, targets, _) = shards.schedule(imps, shards.closures(imps), set(imps),
                                                    dict.fromkeys(imps, 100.0))
        self.assertEqual(len(targets), 8)
        # Low counts put too much work on each runner to qualify even at
        # their lower bound. They are packed, but never simulated.
        self.assertTrue(parts)
        self.assertLessEqual(max(parts), 6)

    def test_no_shard_that_is_no_faster(self):
        # 16000 s of work would take `MAX_SHARDS`; but each sink takes 400 s
        # however many a runner builds at once, as long as 5 or fewer: 8
        # shards are as fast.
        self.assertEqual(self.count(400), 8)

    def test_no_shards_that_save_less_than_their_overhead(self):
        # Small work stays local. Larger independent work can benefit from
        # more than the two shards the old work cutoff would allow.
        self.assertEqual(self.count(10), 0)
        self.assertEqual(self.count(22), 7)


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



class Times(unittest.TestCase):
    """`times`: the build log's time for each module."""

    LOG = "\n".join([
        "✔ [10/90] Built VerifiedGarbage.Spec.A (2.5s)",
        "✔ [11/90] Built VerifiedGarbage.Proof.Framework.Omega (1.2s)",
        "✔ [12/90] Built VerifiedGarbage.Proof.Framework.Omega:c.o (8.8s)",
        "✔ [13/90] Built VerifiedGarbage.Proof.Framework.Omega:dynlib (150ms)",
        "✔ [14/90] Built NativeTactics:shared (209ms)",
        "✔ [15/90] Built VerifiedGarbage.Spec.B (40ms)",
    ])

    def times(self) -> dict[str, float]:
        out = io.StringIO()
        with mock.patch("sys.stdin", io.StringIO(self.LOG)), contextlib.redirect_stdout(out):
            self.assertEqual(shards.main(["times"]), 0)
        return json.loads(out.getvalue())

    def test_a_native_module_s_compile_and_link_are_its_time(self):
        self.assertAlmostEqual(self.times()["VerifiedGarbage.Proof.Framework.Omega"], 1.2 + 8.8 + 0.15)

    def test_modules_and_libraries(self):
        times = self.times()
        self.assertEqual(sorted(times), [
            "VerifiedGarbage.Proof.Framework.Omega",
            "VerifiedGarbage.Spec.A",
            "VerifiedGarbage.Spec.B",
        ])
        self.assertEqual(times["VerifiedGarbage.Spec.A"], 2.5)
        self.assertAlmostEqual(times["VerifiedGarbage.Spec.B"], 0.04)

if __name__ == "__main__":
    unittest.main()
