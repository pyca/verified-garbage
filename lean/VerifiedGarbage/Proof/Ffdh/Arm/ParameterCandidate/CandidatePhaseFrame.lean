module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! A probable-prime phase preserves the candidate octets and public API arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidate_phase_frame {s t : State} {p : CandidateParams} {q : Bool}
    (changed : Frame (phaseRegions (candidatePhase p q) s.sp) s.mem t.mem) :
    Frame (candidateRegions p s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  exact ⟨r, by simpa only [phaseRegions, candidateRegions, candidatePhase, List.mem_cons] using Or.inr hr, fun _ h => h⟩

theorem candidate_header_frame {s t : State} {p : CandidateParams} {q : Bool}
    (nowrap : s.sp.toNat + 72 ≤ 2 ^ 32)
    (changed : Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem) :
    Frame (phaseRegions (candidatePhase p q) s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [phaseRegions], ?_⟩
  rw [VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
  exact Offset.sub _ (by decide) (by decide)

theorem CandidateContext.phase_output {s t : State} {p : CandidateParams} {q : Bool} {consumed : Nat}
    (h : CandidateContext p consumed s)
    (changed : Frame (phaseRegions (candidatePhase p q) s.sp) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length := by
  refine rsa_bytes_frame changed (by have fit : p.out.toNat + p.length ≤ 2 ^ 32 := p.outputFits; omega) ?_
  intro r hr
  simp only [phaseRegions, candidatePhase, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact p.outputScratch
  · exact h.belowOutput.symm
  · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.stackOutput.symm.sub_right (Offset.sub_base _ (by decide : 40 + 28 ≤ 72))

theorem CandidateContext.after_phase {s t : State} {p : CandidateParams} {q : Bool} {consumed next passed : Nat}
    {rs : List Reg} (h : CandidateContext p consumed s) (state : WitnessState (candidatePhase p q) next passed t)
    (changed : Frame (phaseRegions (candidatePhase p q) s.sp) s.mem t.mem) (rest : Rest rs s t) :
    CandidateContext p next t := by
  exact h.after_frame state.usedBound (state.saved.saved 40 (by decide)) (candidate_phase_frame changed) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
