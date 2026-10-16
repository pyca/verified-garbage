import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit importing CRT factors before their secret validation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.savedOperandLayout_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.savedOperandLayout_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.savedOperand
