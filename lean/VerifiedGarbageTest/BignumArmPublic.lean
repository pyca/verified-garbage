import VerifiedGarbage.Artifacts.Rsa.Arm
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the callable ARMv7 checked public operation and its secret-input timing proof. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.public_verified
#assert_standard_axioms VG.Proof.Bignum.Arm.publicBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.publicBody_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.PublicFn.code
