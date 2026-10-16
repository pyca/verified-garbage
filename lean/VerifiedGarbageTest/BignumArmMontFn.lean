import VerifiedGarbage.Proof.Bignum.Arm.MontVerified
import VerifiedGarbage.Artifacts.RsaMont.Arm
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.Restore
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the shared-contract bridge and the wrapper's register restoration. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.montFnBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.montFnBody_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.mont_push_saved
#assert_standard_axioms VG.Proof.Bignum.Arm.mont_restore_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.MontFn.mul

#assert_standard_axioms VG.Proof.Bignum.Arm.mont_verified
#assert_no_compiler_overrides VG.Artifacts.RsaMont.Arm.artifacts
