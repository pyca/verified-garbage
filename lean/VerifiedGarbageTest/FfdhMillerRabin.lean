module

import VerifiedGarbage.Proof.Ffdh.MillerRabin
meta import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! The shared-test bridge is not an emitted artifact yet. Audit its proof
dependencies here so the default build checks its axioms in the meantime. -/

#assert_standard_axioms VG.Proof.Ffdh.rsa_round_eq
#assert_standard_axioms VG.Proof.Ffdh.window_round_eq
