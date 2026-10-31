module

import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit the shared round's AArch64 core proofs before their callable artifacts land. -/

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_ok
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_ct
