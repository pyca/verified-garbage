module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPhaseRun
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedHead
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa

/-! The first or remaining p witness batch has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def limitedPhasePoint (first : Bool) (p : CandidatePoint) : PhasePoint :=
  ⟨limitedPhase p.params first, p.params.out, p.params.length, p.used⟩

private theorem limitedPhaseStart_ok (first : Bool) (p : CandidatePoint) (s : State) (h : CandidateTestStart false p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead false ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s (PhaseStart (limitedPhasePoint first p)) := by
  refine WP.mono (limitedHead_ok h.1 first) ?_
  rintro t ⟨context, saved, changed, _⟩
  have phaseFrame := candidate_header_frame (p := p.params) (q := false) h.1.saved.space.nowrap changed
  have bytes := h.1.phase_output phaseFrame
  exact candidatePhaseInputWithChecks context saved (by rw [bytes]; exact h.2.1)
    (p.params.limited_bounds first).1 (p.params.limited_bounds first).2 h.2.2

theorem limitedTest_ct (v : RoundImpl) (first : Bool) : RelCT isa (Two (CandidateTestStart false))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) (fun _ _ => True) := by
  have limitTrace : RelCT isa (fun s t => s.sp = t.sp)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) (fun s t => s.sp = t.sp) := by
    cases first <;> exact RelCT.block_append
      ((VG.Proof.Bignum.Arm.stackOnly_ct _ rfl).seq (save_ct .r1 52))
  have headerTrace := RelCT.block_append ((phaseHead_ct false).seq limitTrace)
  have head := two_post (headerTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
    (limitedPhaseStart_ok first)
  exact head.seq ((phaseRun_ct v).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨limitedPhasePoint first p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
