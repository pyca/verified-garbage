import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the ARMv7 RSA precomputation body before its public ABI wrapper. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.precompute_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.precompute_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.copyBuffer_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.precompute
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.copyBytes

#assert_standard_axioms VG.Proof.Bignum.Arm.precomputeOut_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exportArray_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.precomputeOut

#assert_standard_axioms VG.Proof.Bignum.Arm.precomputeOut_ct
