import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.RowCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the multiply-accumulate before the RSA registrations use it. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.mac_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.mac_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.mac

#assert_standard_axioms VG.Proof.Bignum.Arm.rowStep_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.rowStep_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.rowStep
