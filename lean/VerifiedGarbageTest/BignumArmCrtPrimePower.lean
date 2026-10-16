import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit factor sanitization, preparation, import and secret exponentiation together. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_primePower_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_primePower_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.primePower
