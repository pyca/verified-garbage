import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete ARMv7 multiply-add row. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.rowFull_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.rowFull_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.rowFull
