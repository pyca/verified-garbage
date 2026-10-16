import VerifiedGarbage.Proof.Bignum.Arm.SubModBuffers
import VerifiedGarbage.Proof.Bignum.Arm.SubModBuffersCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit modular subtraction and its secret-operand timing proof. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.subModBuffers_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.subModBuffers_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.subModBuffers
