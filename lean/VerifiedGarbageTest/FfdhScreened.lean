module

import VerifiedGarbage.Proof.Ffdh.ScreenedSemantics
meta import VerifiedGarbage.Proof.Ffdh.ScreenedSemantics
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit preservation of both complete witness policies and immediate rejection. -/

#assert_standard_axioms VG.Proof.Ffdh.Screened.witnesses_sound
#assert_standard_axioms VG.Proof.Ffdh.Screened.witness_counts
#assert_standard_axioms VG.Proof.Ffdh.Screened.first_failure
