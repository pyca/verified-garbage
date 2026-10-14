import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit carry propagation before the RSA registrations use it. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.rowCarry_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.rowCarry_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.rowCarry
