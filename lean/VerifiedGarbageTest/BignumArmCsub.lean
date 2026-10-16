import VerifiedGarbage.Proof.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit final ARMv7 modular reduction, including secret-bit selection. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.csub_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.csub_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.csub
