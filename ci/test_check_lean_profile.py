"""How `lean_profile.py` reads the build's stored profiles; no builds."""

import contextlib
import io
import json
import pathlib
import tempfile
import unittest

import lean_profile as profile

FILE = "VerifiedGarbage/Proof/A.lean"
# An `.ilean`'s `decls`: name -> [start line, start column, end line, end
# column, ...], 0-based lines, the range including the doc comment.
DECLS = {
    "VG.A.big": [2, 0, 20, 10, 3, 8, 3, 11],
    "VG.A.big.inner": [10, 2, 12, 5, 10, 6, 10, 11],
    "VG.A.small": [22, 0, 23, 4, 22, 8, 22, 13],
}


def info(line, col, *steps):
    return {"level": "info", "message": f"{FILE}:{line}:{col}: " + "\n".join(steps)}


class Steps(unittest.TestCase):
    def test_one_step_per_line_of_a_message(self):
        log = [info(4, 8, "simp took 2.5ms", "type checking took 1.5s")]
        self.assertEqual(list(profile.steps(log)),
                         [(4, 8, "elab", 0.0025), (4, 8, "kernel", 1.5)])

    def test_blocked_is_apart(self):
        log = [info(4, 8, "blocked took 3ms", "blocked (unaccounted) took 1ms")]
        self.assertEqual([k for _, _, k, _ in profile.steps(log)], ["blocked", "blocked"])

    def test_ignores_other_entries(self):
        log = [
            {"level": "trace", "message": ".> LEAN_PATH=… lean -j2 A.lean"},
            {"level": "warning", "message": f"{FILE}:4:8: simp took 2ms"},
            {"level": "info", "message": "stderr:\nparsing took 2ms\ncumulative profiling times:"},
            info(4, 8, "evaluation output, no time"),
        ]
        self.assertEqual(list(profile.steps(log)), [])

    def test_a_repeated_message_counts_once(self):
        log = [info(4, 0, "simp took 2ms"), info(4, 0, "simp took 2ms"), info(5, 0, "simp took 2ms")]
        self.assertEqual(len(list(profile.steps(log))), 2)


class Declaration(unittest.TestCase):
    def test_at_the_name(self):
        # With `Elab.async`, a message is at the declaration's name.
        self.assertEqual(profile.declaration(DECLS, 4, 8), "VG.A.big")

    def test_at_the_doc_comment(self):
        # Without it, at the start of its command: its doc comment.
        self.assertEqual(profile.declaration(DECLS, 3, 0), "VG.A.big")

    def test_innermost(self):
        self.assertEqual(profile.declaration(DECLS, 12, 0), "VG.A.big.inner")

    def test_between_declarations(self):
        self.assertIsNone(profile.declaration(DECLS, 22, 0))
        self.assertIsNone(profile.declaration(DECLS, 1, 0))


class ModuleProfile(unittest.TestCase):
    def test_sums_per_declaration_and_kind(self):
        trace = {"log": [
            info(4, 8, "simp took 10ms", "type checking took 20ms"),
            info(11, 6, "omega took 5ms"),
            info(4, 0, "blocked took 7ms"),
            info(22, 0, "linting took 1ms"),
        ]}
        prof = profile.module_profile(trace, lambda: {"decls": DECLS})
        self.assertEqual(set(prof), {"VG.A.big", "VG.A.big.inner", None})
        self.assertAlmostEqual(prof["VG.A.big"]["elab"], 0.010)
        self.assertAlmostEqual(prof["VG.A.big"]["kernel"], 0.020)
        self.assertAlmostEqual(prof["VG.A.big"]["blocked"], 0.007)
        self.assertAlmostEqual(prof["VG.A.big.inner"]["elab"], 0.005)
        self.assertAlmostEqual(prof[None]["elab"], 0.001)

    def test_reads_no_ilean_without_a_profile(self):
        def fail():
            raise AssertionError("read the .ilean")
        self.assertEqual(profile.module_profile({"log": []}, fail), {})


class Main(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.build = pathlib.Path(tmp.name)
        self.write("VerifiedGarbage/Proof/A", [
            info(4, 8, "type checking took 3s", "simp took 1s"),
            info(23, 8, "simp took 2s", "blocked took 9s"),
        ], DECLS)
        self.write("VerifiedGarbage/Proof/B", [info(1, 8, "type checking took 1s")],
                   {"VG.B.only": [0, 0, 2, 0, 0, 8, 0, 12]})
        # Built before the profiler was on.
        self.write("VerifiedGarbage/Spec/C", [], {})

    def write(self, mod, log, decls):
        path = self.build / mod
        path.parent.mkdir(parents=True, exist_ok=True)
        path.with_suffix(".trace").write_text(json.dumps({"log": log}))
        path.with_suffix(".ilean").write_text(json.dumps({"decls": decls}))

    def run_main(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            profile.main(["--build", str(self.build), *args])
        return out.getvalue(), err.getvalue()

    def test_ranks_by_total_without_blocked(self):
        out, err = self.run_main("--json")
        rows = json.loads(out)
        self.assertEqual([(r["module"], r["decl"]) for r in rows], [
            ("VerifiedGarbage.Proof.A", "VG.A.big"),
            ("VerifiedGarbage.Proof.A", "VG.A.small"),
            ("VerifiedGarbage.Proof.B", "VG.B.only"),
        ])
        self.assertEqual(rows[1]["blocked"], 9.0)

    def test_sort_by_kernel(self):
        out, _ = self.run_main("--json", "--sort", "kernel")
        self.assertEqual([r["decl"] for r in json.loads(out)], ["VG.A.big", "VG.B.only", "VG.A.small"])

    def test_by_module_and_prefix(self):
        out, _ = self.run_main("--json", "--by", "module", "--module", "VerifiedGarbage.Proof.B")
        self.assertEqual(json.loads(out), [{"module": "VerifiedGarbage.Proof.B", "decl": None,
                                            "kernel": 1.0, "elab": 0.0, "blocked": 0.0}])

    def test_table_and_unprofiled_count(self):
        out, err = self.run_main("--top", "1")
        self.assertEqual(out.splitlines()[1].split(), ["4.00", "3.00", "1.00", "0.00", "VG.A.big",
                                                       "(VerifiedGarbage.Proof.A)"])
        self.assertEqual(len(out.splitlines()), 2)
        self.assertIn("1 modules' logs held no profile", err)

    def test_no_profile_at_all(self):
        with self.assertRaises(SystemExit):
            self.run_main("--module", "VerifiedGarbage.Spec")


if __name__ == "__main__":
    unittest.main()
