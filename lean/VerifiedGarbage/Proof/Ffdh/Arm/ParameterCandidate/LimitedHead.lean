module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitStore
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseHeader
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Limit a prepared p header while preserving all candidate metadata and tape counters. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem limitedHead_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (first : Bool) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead false ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s fun t =>
      CandidateContext p used t ∧ SavedFrame (witnessValues (limitedPhase p first) used 0) witnessSlots t ∧
      Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.block_append_iff]
  refine WP.mono (candidatePhaseHead_ok h false) ?_
  rintro u ⟨ctx, saved, changed, rest⟩
  have checks : 0 < Spec.Ffdh.primeChecks p.bits := by unfold Spec.Ffdh.primeChecks; split <;> decide
  refine WP.mono (phaseLimit_ok first checks ctx.saved.space (saved.saved 52 (by decide))) ?_
  rintro t ⟨memory, restT⟩
  have frame : Frame [⟨State.addr (u.sp + 44#32), 16⟩] u.mem t.mem := by
    rw [memory]
    refine (Frame.refl _ _).writeW (r := ⟨State.addr (u.sp + 44#32), 16⟩) (by simp) _ ?_
    rw [VG.Arm.addr_add (by have := ctx.saved.space.nowrap; omega),
      VG.Arm.addr_add (by have := ctx.saved.space.nowrap; omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have usedWord : t.mem.readW (State.addr (t.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    rw [restT.sp, memory, phaseStore_word _ _ ctx.saved.space.nowrap (by decide) (by decide) (by decide) _]
    exact ctx.saved.saved 40 (by decide)
  have phaseFrame := candidate_header_frame (p := p) (q := false) ctx.saved.space.nowrap frame
  refine ⟨ctx.after_frame ctx.consumedBound usedWord (candidate_phase_frame phaseFrame) restT, ?_, ?_,
    rest.trans (restT.mono (by simp [roundClobbers]))⟩
  · refine ⟨by rw [restT.sp]; exact saved.space.congr restT.wr, ?_⟩
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [restT.sp, memory, phaseStore_word _ _ ctx.saved.space.nowrap (by decide) (by decide) (by decide) _]
    all_goals first | rfl | exact saved.saved _ (by decide)
  · rw [rest.sp] at frame
    exact changed.trans frame

end VG.Proof.Ffdh.Arm.ParameterCandidate
