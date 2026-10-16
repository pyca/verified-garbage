import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit initialization of the ARMv7 packed-word accumulator. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.zero_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.zero_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.zero
