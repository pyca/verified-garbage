import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit switching between CRT arithmetic workspaces. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_saveMain_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_saveMain_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_selectChild_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_selectChild_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_selectMain_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_selectMain_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.selectChild
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.selectMain
