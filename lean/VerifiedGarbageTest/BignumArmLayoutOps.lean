import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit import, comparison and workspace switching before secret-factor validation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.importOperandLayout_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.importOperandLayout_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.inputCompareLayout_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.inputCompareLayout_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.activateWorkspace_ready
#assert_standard_axioms VG.Proof.Bignum.Arm.activateWorkspace_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.activateWorkspace
