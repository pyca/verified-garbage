import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.MontMixedProduct
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit private-key reloading and multiplication used in CRT recombination. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.savedOperand_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.savedOperand_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.montMixedProduct_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.savedOperand
