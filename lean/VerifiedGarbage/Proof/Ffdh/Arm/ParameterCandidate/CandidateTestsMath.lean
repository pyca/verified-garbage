module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ScreenedTestsMath

/-! The native candidate uses the reviewed early-p witness policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidateTests (p : CandidateParams) (used : Nat) : Option (Bool × List Byte) := screenedTests p used

end VG.Proof.Ffdh.Arm.ParameterCandidate
