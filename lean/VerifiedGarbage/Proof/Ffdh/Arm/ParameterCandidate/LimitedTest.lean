module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseRun
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! One limited p batch with exact shared witness-stream consumption. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def LimitedTestEnd (p : CandidateParams) (first : Bool) (used : Nat) (s t : State) : Prop :=
  ∃ next, CandidateContext p next t ∧ used ≤ next ∧
    t.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining (limitedPhase p first) used 0)) ∧
    (∀ pass rest, witnessRemaining (limitedPhase p first) used 0 = some (pass, rest) → rest = p.bytes.drop next) ∧
    Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
    Frame (phaseRegions (limitedPhase p first) s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem limitedTest_ok (v : RoundImpl) {s : State} {p : CandidateParams} {consumed : Nat} {first : Bool}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (limitedPhase p first).modulus)
    (odd : (limitedPhase p first).modulus % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) s (LimitedTestEnd p first consumed s) := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited, WP.seq_iff]
  refine WP.mono (limitedHead_ok h first) ?_
  rintro u ⟨context, saved, changed, rest⟩
  have phaseFrame := candidate_header_frame (p := p) (q := false) h.saved.space.nowrap changed
  have bytes := h.phase_output phaseFrame
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) =
      (limitedPhase p first).modulus := by rw [bytes]; exact number
  refine WP.mono (phaseRun_ok v (candidatePhaseInputWithChecks context saved numberU (p.limited_bounds first).1 (p.limited_bounds first).2 odd)) ?_
  rintro t ⟨next, passed, state, consumedT, status, suffix, changedT, restT⟩
  have bytesT := context.phase_output (q := false) changedT
  have contextT := context.after_frame state.usedBound (state.saved.saved 40 (by decide))
    (candidate_phase_frame (p := p) (q := false) changedT) restT
  rw [rest.sp] at changedT
  exact ⟨next, contextT, consumedT, status, suffix, bytesT.trans bytes, phaseFrame.trans changedT, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
