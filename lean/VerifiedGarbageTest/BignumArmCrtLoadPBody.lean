import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPBodyCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit importing p and qInv and accumulating their secret range check. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_loadPBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_loadPBody_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.CrtFn.loadPBody
