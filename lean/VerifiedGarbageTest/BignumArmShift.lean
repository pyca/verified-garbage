import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the in-place packed-word shift for ARMv7 RSA. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.shift_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.shift_quotient
#assert_standard_axioms VG.Proof.Bignum.Arm.shift_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.shift
