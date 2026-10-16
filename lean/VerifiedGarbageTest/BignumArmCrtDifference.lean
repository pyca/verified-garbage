import VerifiedGarbage.Proof.Bignum.Arm.CrtDifferenceCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit reduction and subtraction of the two CRT residues. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_difference_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_difference_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.difference
