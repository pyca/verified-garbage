import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
import VerifiedGarbage.Proof.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit serialization, input comparison, and branchless rejection masking. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.exportBE_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exportBE_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.inputCompare_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.inputCompare_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.maskBuffer_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.maskBytes_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.exportBE
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.inputCompare
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.maskBytes
