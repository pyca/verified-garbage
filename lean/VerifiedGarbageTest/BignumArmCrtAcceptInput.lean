import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptInputCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the private RSA input import and secret range check. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_acceptInput_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_acceptInput_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.CrtFn.acceptInput
