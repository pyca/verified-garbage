module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers

/-! Candidate returns use public output addresses and width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch

def CandidateContextStart (p : CandidatePoint) (s : State) : Prop := CandidateContext p.params p.used s

theorem candidateRejected_ct : RelCT isa (Two CandidateContextStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected (fun _ _ => True) :=
  two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩ : ResultData))
    (fun p _ h => ⟨p.used, h.result_context⟩) finRejected_ct

theorem candidateNone_ct : RelCT isa (Two CandidateContextStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (fun _ _ => True) :=
  two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩ : ResultData))
    (fun p _ h => ⟨p.used, h.result_context⟩) finNone_ct

end VG.Proof.Ffdh.Arm.ParameterCandidate
