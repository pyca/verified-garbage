import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit modular doubling used by ARMv7 RSA key precomputation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.doubleBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.doubleBody_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.doubleBody
