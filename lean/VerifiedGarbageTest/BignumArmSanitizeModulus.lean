import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit secret factor sanitization before modular arithmetic. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.sanitizeModulus_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.sanitizeModulus_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.sanitizeModulus
