import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubRowCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit packed-word subtraction, including a secret incoming borrow. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.subRow_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.subRow_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.subRow
