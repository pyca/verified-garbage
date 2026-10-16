import VerifiedGarbage.Artifacts.Rsa.Arm
import VerifiedGarbage.Proof.Bignum.Arm.PcFn
import VerifiedGarbage.Proof.Bignum.Arm.PcFnCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit ARMv7 RSA precomputation and its public ABI wrapper. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.precompute_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.precompute_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.copyBuffer_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.precompute
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.copyBytes

#assert_standard_axioms VG.Proof.Bignum.Arm.precomputeOut_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exportArray_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.precomputeOut

#assert_standard_axioms VG.Proof.Bignum.Arm.precomputeOut_ct

#assert_standard_axioms VG.Proof.Bignum.Arm.modulusCheck_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.modulusCheck_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.modulusCheck

#assert_standard_axioms VG.Proof.Bignum.Arm.pcBody_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.PcFn.body

#assert_standard_axioms VG.Proof.Bignum.Arm.pcFn_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.pcFail_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.PcFn.code

#assert_standard_axioms VG.Proof.Bignum.Arm.pcFn_ct

#assert_standard_axioms VG.Proof.Bignum.Arm.precompute_verified
#assert_no_compiler_overrides VG.Artifacts.Rsa.Arm.artifacts
