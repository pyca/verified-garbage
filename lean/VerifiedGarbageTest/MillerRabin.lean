module

import VerifiedGarbage.Proof.MillerRabin.Representation
meta import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit the shared round's target-independent lemmas (each target's core
proofs: `MillerRabinX86_64.lean`, `MillerRabinAArch64.lean`). -/

#assert_standard_axioms VG.Proof.MillerRabin.round_mod
#assert_standard_axioms VG.Proof.MillerRabin.witness_exists

#assert_standard_axioms VG.Proof.MillerRabin.round_eq_of_mont
