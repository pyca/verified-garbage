import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffers
import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffersCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit exact multiword equality and its secret-operand timing proof. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.equalBuffers_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.equalBuffers_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.equalBuffers
