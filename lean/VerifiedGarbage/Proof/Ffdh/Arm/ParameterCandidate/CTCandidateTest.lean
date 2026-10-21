module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPhaseRun
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! The full q or p candidate test has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidatePoint where
  params : CandidateParams
  used : Nat

def CandidateTestStart (q : Bool) (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = (candidatePhase p.params q).modulus ∧
  (candidatePhase p.params q).modulus % 2 = 1

private def candidatePhasePoint (q : Bool) (p : CandidatePoint) : PhasePoint :=
  ⟨candidatePhase p.params q, p.params.out, p.params.length, p.used⟩

private theorem candidatePhaseStart_ok (q : Bool) (p : CandidatePoint) (s : State) (h : CandidateTestStart q p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s (PhaseStart (candidatePhasePoint q p)) := by
  refine WP.mono (candidatePhaseHead_ok h.1 q) ?_
  rintro t ⟨context, saved, changed, _⟩
  have phaseFrame := candidate_header_frame (p := p.params) (q := q) h.1.saved.space.nowrap changed
  have bytes := h.1.phase_output phaseFrame
  exact candidatePhaseInput context saved (by rw [bytes]; exact h.2.1) h.2.2

theorem candidateTest_ct (v : RoundImpl) (q : Bool) : RelCT isa (Two (CandidateTestStart q))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.test q v.name v.code) (fun _ _ => True) := by
  have head := two_post ((phaseHead_ct q).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
    (candidatePhaseStart_ok q)
  exact head.seq ((phaseRun_ct v).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨candidatePhasePoint q p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
