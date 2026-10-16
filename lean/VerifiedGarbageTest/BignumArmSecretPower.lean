import VerifiedGarbage.Proof.Bignum.Arm.SecretPowerCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete ciphertext-import and secret-power operation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.secretPower_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.secretPower_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.secretPower
