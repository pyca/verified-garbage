module

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Backend
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Backend
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit the functional and callable domain validator proofs. -/

#assert_standard_axioms VG.Proof.Ffdh.X86_64.CheckDomain.cd_correct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.CheckDomain.cd_implies

#assert_standard_axioms VG.Proof.Ffdh.X86_64.CheckDomain.domainCode_verified
