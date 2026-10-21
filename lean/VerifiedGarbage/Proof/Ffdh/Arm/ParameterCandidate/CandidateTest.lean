module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseRun
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! A complete candidate q/p test with exact shared witness-stream consumption. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestEnd (p : CandidateParams) (q : Bool) (used : Nat) (s t : State) : Prop :=
  ∃ next, CandidateContext p next t ∧ used ≤ next ∧
    t.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining (candidatePhase p q) used 0)) ∧
    (∀ pass rest, witnessRemaining (candidatePhase p q) used 0 = some (pass, rest) → rest = p.bytes.drop next) ∧
    Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
    Frame (phaseRegions (candidatePhase p q) s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem candidateTest_ok (v : RoundImpl) {s : State} {p : CandidateParams} {consumed : Nat} {q : Bool}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (candidatePhase p q).modulus)
    (odd : (candidatePhase p q).modulus % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.test q v.name v.code) s (CandidateTestEnd p q consumed s) := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.test, WP.seq_iff]
  refine WP.mono (candidatePhaseHead_ok h q) ?_
  rintro u ⟨context, saved, changed, rest⟩
  have phaseFrame := candidate_header_frame (p := p) (q := q) h.saved.space.nowrap changed
  have bytes := h.phase_output phaseFrame
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) =
      (candidatePhase p q).modulus := by rw [bytes]; exact number
  refine WP.mono (phaseRun_ok v (candidatePhaseInput context saved numberU odd)) ?_
  rintro t ⟨next, passed, state, consumedT, status, suffix, changedT, restT⟩
  have bytesT := context.phase_output changedT
  have contextT := context.after_phase state changedT restT
  rw [rest.sp] at changedT
  exact ⟨next, contextT, consumedT, status, suffix, bytesT.trans bytes, phaseFrame.trans changedT, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
