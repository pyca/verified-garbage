import VerifiedGarbage.Proof.Bignum.Arm.CrtTimesInverseCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit multiplication of the CRT residue difference by the secret inverse. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_timesInverse_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_timesInverse_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.timesInverse
