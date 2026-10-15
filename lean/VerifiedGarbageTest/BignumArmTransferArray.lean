import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit exact cross-workspace RSA residue transfer and its leakage bound. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.transferArray_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.transferArray_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.transferArray
