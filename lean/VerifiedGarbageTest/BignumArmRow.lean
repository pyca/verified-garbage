import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the variable-width row before the RSA registrations use it. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.row_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.row_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.row
