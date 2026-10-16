import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the complete wide CRT reconstruction and its leakage bound. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_recombine_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_recombine_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.Crt.recombine
