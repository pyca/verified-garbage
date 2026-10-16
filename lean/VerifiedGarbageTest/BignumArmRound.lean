import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete ARMv7 Montgomery round and its complete scanning loop. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.montRound_ok
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.montRound

#assert_standard_axioms VG.Proof.Bignum.Arm.montRounds_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.montRounds_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.montRounds

#assert_standard_axioms VG.Proof.Bignum.Arm.montCore_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.montCore_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.montCore

#assert_standard_axioms VG.Proof.Bignum.Arm.montBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.montBody_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.montBody
