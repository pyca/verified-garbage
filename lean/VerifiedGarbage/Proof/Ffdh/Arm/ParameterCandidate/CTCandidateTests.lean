module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedTests

/-! The screened native controller depends only on the same public candidate and entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestsStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateTestStart true p s ∧ p.params.length ≤ p.params.bytes.length

theorem candidateTests_ct (v : RoundImpl) : RelCT isa (Two CandidateTestsStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code) (fun _ _ => True) :=
  (screenedTests_ct v).mono
    (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.2, h.1.2.2⟩) h) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
