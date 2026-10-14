import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! The ARMv7 RSA arithmetic foundation is not yet an emitted API. Audit its
universal correctness and constant-time theorems directly until it is also
reachable through the RSA artifact registrations. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.wideMul_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.wideMul_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.wideMul
