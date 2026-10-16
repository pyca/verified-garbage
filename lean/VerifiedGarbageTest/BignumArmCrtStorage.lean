import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.TCB.Axioms

/-! Audit that the three CRT workspaces fit the existing scratch permissions. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.crt_storage_addresses
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_regions_covered
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_expanded_context
#assert_standard_axioms VG.Proof.Bignum.Arm.crt_expanded_covers
