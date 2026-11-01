module

import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ws

/-! Audit the shared FFDH pieces before registering the domain operations. -/

#assert_standard_axioms VG.Proof.Ffdh.X86_64.wsSetup_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.modSetup_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ltArr_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.geArr_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.eqArr_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ltP_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.isOdd_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.range_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ltArr_ct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.geArr_ct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.eqArr_ct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.pow_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.pow_ct
