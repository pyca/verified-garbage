import VerifiedGarbage.Proof.Bignum.Arm.PreparePrimeCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit secret-factor sanitization, inverse and R-squared precomputation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.preparePrime_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.preparePrime_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.preparePrime
