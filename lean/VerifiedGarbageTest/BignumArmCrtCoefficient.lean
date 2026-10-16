import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the full signed-difference and inverse multiplication used by RSA CRT. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_coefficient_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_coefficient_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.coefficient
