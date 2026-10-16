import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.SetBasesCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit construction of the existing shared RSA workspace layout. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.setup_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.setup_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.setBases_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.setBases_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.setup

#assert_standard_axioms VG.Proof.Bignum.Arm.setSmallFn_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.setSmallFn_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.setSmallFn
