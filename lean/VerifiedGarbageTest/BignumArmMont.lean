import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.TCB.Audit
import VerifiedGarbage.TCB.Axioms

/-! Audit the packed-word Montgomery identities used by ARMv7 RSA. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.round_sum_lt
#assert_standard_axioms VG.Proof.Bignum.Arm.round_lt
#assert_standard_axioms VG.Proof.Bignum.Arm.round_mod
#assert_standard_axioms VG.Proof.Bignum.Arm.round_step
#assert_standard_axioms VG.Proof.Bignum.Arm.mont_low
#assert_standard_axioms VG.Proof.Bignum.Arm.inverse32
#assert_standard_axioms VG.Proof.Bignum.Arm.radix32

#assert_standard_axioms VG.Proof.Bignum.Arm.csub_result
#assert_standard_axioms VG.Proof.Bignum.Arm.subWord_value
#assert_standard_axioms VG.Proof.Bignum.Arm.subBorrow_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.subBorrow_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.subBorrow
