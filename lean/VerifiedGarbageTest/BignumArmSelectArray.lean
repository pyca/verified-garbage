import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit branchless workspace selection, including modulus replacement. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.selectArray_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.selectArray_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.selectArray
