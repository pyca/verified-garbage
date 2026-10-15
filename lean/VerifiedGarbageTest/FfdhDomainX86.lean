import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
import VerifiedGarbage.TCB.Axioms

/-! Audit the functional domain validator before registering its callable artifact. -/

#assert_standard_axioms VG.Proof.Ffdh.X86_64.CheckDomain.cd_correct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.CheckDomain.cd_implies
