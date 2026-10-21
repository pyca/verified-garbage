module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessProgress
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResult
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd

/-! Final return timing depends on public status and buffer addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidatePhaseResult (q : Bool) (p : CandidatePoint) (s : State) : Prop :=
  (∃ next, CandidateContext p.params next s) ∧
  s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining (candidatePhase p.params q) p.used 0))

theorem candidateTestResult_ct (v : RoundImpl) (q : Bool) : RelCT isa (Two (CandidateTestStart q))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.test q v.name v.code) (Two (CandidatePhaseResult q)) :=
  two_post (candidateTest_ct v q) (fun _ _ h => WP.mono (candidateTest_ok v h.1 h.2.1 h.2.2)
    (fun _ ⟨next, ctx, _, status, _, _, _, _⟩ => ⟨⟨next, ctx⟩, status⟩))

theorem candidatePhaseResult_ct (q : Bool) : RelCT isa (Two (CandidatePhaseResult q))
    VG.Impl.Ffdh.Arm.ParameterCandidate.result (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩,
    witnessResultStatus (witnessRemaining (candidatePhase p.params q) p.used 0))) ?_ result_ct
  intro p s h
  obtain ⟨next, ctx⟩ := h.1
  exact ⟨⟨next, ctx.result_context⟩, witnessResultStatus_bound _, h.2⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
