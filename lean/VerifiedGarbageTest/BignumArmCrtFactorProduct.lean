import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProductCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit complete CRT factor multiplication, including zeroing and header setup. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_factorProduct_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_factorProduct_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.factorProduct
