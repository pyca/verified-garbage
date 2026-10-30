"""What `check_lean_speed.py`'s native hint rule rejects; no builds."""

import unittest

import check_lean_speed

DATA = "meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData\n"
CALL = "theorem ct : P := by native_taint_decide_sum [mulSum]\n"


class NativeHints(unittest.TestCase):
    def problems(self, module: str, text: str) -> list[str]:
        return [what for _, what in check_lean_speed.native_hints(module, text)]

    def test_a_call_with_its_hint_data(self):
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", DATA + CALL), [])

    def test_public_meta_import_counts(self):
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", "public " + DATA + CALL), [])

    def test_a_call_without_it(self):
        [p] = self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", CALL)
        self.assertIn("meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData", p)

    def test_the_target_is_the_modules(self):
        # Arm's hint data does not serve an x86 module.
        arm = DATA.replace(".X86.", ".Arm.")
        [p] = self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", arm + CALL)
        self.assertIn(".X86.NativeHintData", p)
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Aes.Arm.Ctr32", arm + CALL), [])

    def test_a_private_import_does_not_count(self):
        text = "import VerifiedGarbage.Proof.Framework.X86.NativeHintData\n" + CALL
        self.assertEqual(len(self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", text)), 1)

    def test_a_target_without_a_native_domain(self):
        [p] = self.problems("VerifiedGarbage.Proof.Sha256.X86_64.Compress", CALL)
        self.assertIn("use `taint_decide_sum`", p)

    def test_comments_and_the_framework_are_skipped(self):
        commented = "-- native_taint_decide falls back without its data\n/- native_taint_decide -/\n"
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified", commented), [])
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Framework.NativeTaintCore", CALL), [])

    def test_a_longer_name_is_not_a_call(self):
        self.assertEqual(self.problems("VerifiedGarbage.Proof.Ecdh.X86.P521.Verified",
                                       "theorem t := VG.native_taint_decide_lemma\n"), [])


if __name__ == "__main__":
    unittest.main()
