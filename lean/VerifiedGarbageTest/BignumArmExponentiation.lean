import VerifiedGarbage.Proof.Bignum.Arm.ExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
import VerifiedGarbage.Proof.Bignum.Arm.ExpBytes
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the arithmetic and bit-loop building blocks for ARMv7 RSA exponentiation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.montOp_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.montOp_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.expInit_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.expBits_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exp_finish_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.expInit
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.expBits

#assert_standard_axioms VG.Proof.Bignum.Arm.expBytes_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.expBytes

#assert_standard_axioms VG.Proof.Bignum.Arm.expBits_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.expByteHead_ct

#assert_standard_axioms VG.Proof.Bignum.Arm.expPhase_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.expPhase_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.expPhase
