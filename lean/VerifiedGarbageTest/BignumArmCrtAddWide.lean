import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit exact carry propagation and secret-independent CRT addition. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_addWide_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_addWide_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.addWide
