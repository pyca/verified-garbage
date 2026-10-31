module

import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ResidentBackend
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ResidentBackend
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk

/-!
# Axiom audits of individual theorems

Checks of theorems that are not artifacts. The audit reads what each
depends on from the records of the modules that declare them
(`TCB/AuditRecords.lean`).
-/

#assert_standard_axioms VG.Proof.Sha3.AArch64.Neon.X2.verified
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.Resident.functional
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.absorb_correct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_ct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_verified
#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.absorbBlock_ok
#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.permute_verified
#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.hardware_absorb_correct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bulk_correct
