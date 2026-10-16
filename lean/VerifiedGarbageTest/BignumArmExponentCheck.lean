import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete ARMv7 public-exponent validator. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.exponentCheck_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exponentCheck_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.exponentCheck
