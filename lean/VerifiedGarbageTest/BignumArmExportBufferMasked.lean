import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMaskedCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit accepted CRT serialization and secret rejection masking. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.exportBufferMasked_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.exportBufferMasked_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.exportBufferMasked
