import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAllCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete CRT workspace initialization and public buffer layout. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_layout_fits
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_setupAll_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_setupAll_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.setupAll
