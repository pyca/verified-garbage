"""The bulk import trim's rounds, cache and state, with the check stubbed;
no builds."""

import json
import pathlib
import tempfile
import unittest
from unittest import mock

import check_lean_public_imports as check
import trim_lean_imports as trim


class Trim(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.lean = self.root / "lean"
        for target, value in ((check, "LEAN"), (check, "ROOT")):
            patch = mock.patch.object(target, value, self.lean if value == "LEAN" else self.root)
            patch.start()
            self.addCleanup(patch.stop)
        self.trace("VerifiedGarbage.A", "aaaa")
        self.state = trim.State(self.root / "state.json")

    def trace(self, mod, dep):
        p = self.lean / ".lake/build/lib/lean" / pathlib.Path(*mod.split(".")).with_suffix(".trace")
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps({"depHash": dep, "outputs": {"o": [f"{dep}.olean"]}}))

    def test_the_key_is_lakes_hash_of_inputs_and_outputs(self):
        self.assertEqual(trim.trace_key("VerifiedGarbage.A"), "aaaa:aaaa.olean")
        self.assertIsNone(trim.trace_key("VerifiedGarbage.Unbuilt"))

    def test_an_unchanged_module_is_not_shaken_again(self):
        path = str(check.graph_path("VerifiedGarbage.A"))
        out = f"{path}:\n  remove #[import VerifiedGarbage.B]\n"
        with mock.patch.object(check, "build_modules"), mock.patch.object(check, "shake", return_value=out) as shake:
            self.assertEqual(trim.shaken(["VerifiedGarbage.A"], self.state, 10),
                             {path: (["import VerifiedGarbage.B"], [])})
            trim.shaken(["VerifiedGarbage.A"], trim.State(self.state.path), 10)
            self.assertEqual(shake.call_count, 1)
            # A new build of A: shaken again.
            self.trace("VerifiedGarbage.A", "bbbb")
            trim.shaken(["VerifiedGarbage.A"], trim.State(self.state.path), 10)
            self.assertEqual(shake.call_count, 2)

    def test_uses_are_cached_by_build(self):
        with mock.patch.object(check, "module_uses", return_value={"VerifiedGarbage.A": {"X"}}) as read:
            uses = trim.cached_uses(self.state)
            self.assertEqual(uses(["VerifiedGarbage.A"], "public"), {"VerifiedGarbage.A": {"X"}})
            self.assertEqual(uses(["VerifiedGarbage.A"], "public"), {"VerifiedGarbage.A": {"X"}})
            self.assertEqual(read.call_count, 1)

    def test_what_is_not_applied(self):
        undone = "lean/VerifiedGarbage/A.lean:4: `import VerifiedGarbage.B`: VerifiedGarbage.A does not use it: remove it"
        self.state.undone.add(undone)
        self.assertFalse(trim.usable(undone, self.state))
        registration = ("lean/VerifiedGarbage/Proof/C.lean:3: `public import VerifiedGarbage.Proof.B`: … make it "
                        "`import VerifiedGarbage.Proof.B`, and import what it passed on where it is used: "
                        "VerifiedGarbage.Generic.X.Y uses VerifiedGarbage.Proof.B")
        self.assertFalse(trim.usable(registration, self.state))
        self.assertTrue(trim.usable(registration.replace("Generic.X.Y", "Proof.D"), self.state))
        self.assertTrue(trim.reviewed("VerifiedGarbage.Artifacts.Aes.X86"))
        self.assertFalse(trim.reviewed("VerifiedGarbage.Proof.Generics"))

    def run_rounds(self, findings, fixes):
        with mock.patch.object(trim, "shaken", return_value={}), \
                mock.patch.object(check, "Graph"), mock.patch.object(check, "dependency_roots", return_value=[]), \
                mock.patch.object(check, "problems", side_effect=findings), \
                mock.patch.object(check, "fix_and_verify", side_effect=fixes) as fix:
            return trim.trim(["VerifiedGarbage.A"], ["VerifiedGarbage.A"], 5, 10, self.state), fix

    def test_rounds_stop_when_nothing_is_left(self):
        f = "lean/VerifiedGarbage/A.lean:4: `import VerifiedGarbage.B`: VerifiedGarbage.A does not use it: remove it"
        totals, fix = self.run_rounds([[f], []], [(["lean/VerifiedGarbage/A.lean: remove VerifiedGarbage.B"], [])])
        self.assertEqual(totals, {"rounds": 2, "applied": 1, "undone": 0})
        self.assertEqual(fix.call_count, 1)

    def test_an_undone_finding_is_not_tried_again(self):
        f = "lean/VerifiedGarbage/A.lean:4: `import VerifiedGarbage.B`: VerifiedGarbage.A does not use it: remove it"
        # Round 1 undoes it; round 2 finds it again and skips it: no progress.
        totals, fix = self.run_rounds([[f], [f]], [([], ["VerifiedGarbage.A"])])
        self.assertEqual(totals["undone"], 1)
        self.assertEqual(fix.call_count, 1)
        self.assertIn(f, trim.State(self.state.path).undone)


if __name__ == "__main__":
    unittest.main()
