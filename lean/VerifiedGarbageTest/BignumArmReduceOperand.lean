import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit full-width operand reduction through Montgomery encoding and decoding. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.montEncode_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.reduceOperand_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.reduceOperand_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.reduceOperand
