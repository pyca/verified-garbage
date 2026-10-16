import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit multiword selection controlled by a secret bit. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.selectRow_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.selectRow_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.selectRow
