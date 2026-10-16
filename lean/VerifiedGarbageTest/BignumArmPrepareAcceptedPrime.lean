import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the secret acceptance handoff and sanitized factor preparation together. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.prepareAcceptedPrime_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.prepareAcceptedPrime_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.prepareAcceptedPrime
