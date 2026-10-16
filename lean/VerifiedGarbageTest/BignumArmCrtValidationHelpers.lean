import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit extended-buffer clearing and secret validation-bit conjunction. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_clearWide_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_clearWide_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.mergeAcceptance_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.mergeAcceptance_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.validation_bits_and
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.clearWide
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.mergeAcceptance
