import VerifiedGarbage.Proof.Bignum.Arm.SecretExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.SecretExpPhaseCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the private exponentiation phase, including distinct-secret-exponent leakage. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.secretExpPhase_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.secretExpPhase_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.secretExpPhase
