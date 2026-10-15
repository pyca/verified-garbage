import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit complete array modular subtraction and carry-word initialization. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.subModArray_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.subModArray_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.subModArray
