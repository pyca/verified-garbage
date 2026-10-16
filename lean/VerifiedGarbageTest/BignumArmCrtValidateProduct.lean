import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProductCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit multiplication and full-width comparison as one validation operation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_validateProduct_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_validateProduct_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.validateProduct
