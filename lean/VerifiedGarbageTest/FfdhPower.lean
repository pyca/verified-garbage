module

import VerifiedGarbage.Proof.Ffdh.Power
meta import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit closure of powers of a checked FFDH generator. -/

#assert_standard_axioms VG.Proof.Ffdh.power_subgroup
#assert_standard_axioms VG.Proof.Ffdh.parametersValid_generator
#assert_standard_axioms VG.Proof.Ffdh.publicValid_power
