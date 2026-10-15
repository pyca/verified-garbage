import VerifiedGarbage.Proof.Bignum.Arm.WideProductCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit exact wide multiplication and its secret-operand timing proof. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.wideProduct_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.wideProduct_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.wideProduct
