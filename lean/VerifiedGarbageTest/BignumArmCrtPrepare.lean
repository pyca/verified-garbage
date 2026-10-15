import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit full private RSA workspace preparation and modulus import. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_prepare_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_prepare_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.CrtFn.prepare
