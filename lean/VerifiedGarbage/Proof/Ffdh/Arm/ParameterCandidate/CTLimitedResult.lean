module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLimitedTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResult
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams

/-! Return a public witness-engine answer regardless of which batch produced it. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateAnswerResult (answer : CandidatePoint → Option (Bool × List Byte)) (p : CandidatePoint) (s : State) : Prop :=
  (∃ next, CandidateContext p.params next s) ∧ s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (answer p))

def limitedAnswer (first : Bool) (p : CandidatePoint) : Option (Bool × List Byte) :=
  witnessRemaining (limitedPhase p.params first) p.used 0

theorem limitedTestResult_ct (v : RoundImpl) (first : Bool) : RelCT isa (Two (CandidateTestStart false))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) (Two (CandidateAnswerResult (limitedAnswer first))) :=
  two_post (limitedTest_ct v first) (fun _ _ h => WP.mono (limitedTest_ok v h.1 h.2.1 h.2.2)
    (fun _ ⟨next, ctx, _, status, _, _, _, _⟩ => ⟨⟨next, ctx⟩, status⟩))

theorem candidateAnswerResult_ct (answer : CandidatePoint → Option (Bool × List Byte)) :
    RelCT isa (Two (CandidateAnswerResult answer)) VG.Impl.Ffdh.Arm.ParameterCandidate.result (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩, witnessResultStatus (answer p))) ?_ result_ct
  intro p s h
  obtain ⟨next, ctx⟩ := h.1
  exact ⟨⟨next, ctx.result_context⟩, witnessResultStatus_bound _, h.2⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
