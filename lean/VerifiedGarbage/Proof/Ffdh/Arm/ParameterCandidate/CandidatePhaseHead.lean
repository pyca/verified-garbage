module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseHeader
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize the q/p policy without changing candidate metadata or entropy accounting. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidatePhaseHead_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (q : Bool) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      CandidateContext p consumed t ∧
      SavedFrame (witnessValues (candidatePhase p q) consumed 0) witnessSlots t ∧
      Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have bits : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 p.bits :=
    h.saved.saved 24 (by decide)
  refine WP.mono (phaseHead_ok q s p.minBits p.maxBits h.saved.space bits) ?_
  rintro t ⟨memory, rest⟩
  have changed : Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem := by
    rw [memory]
    exact phaseMemory_frame q p.bits h.saved.space.nowrap
  have candidateChanged : Frame (candidateRegions p s.sp) s.mem t.mem := by
    refine changed.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.sub _ (by decide) (by decide)
  have context : CandidateContext p consumed t := by
    refine h.after_frame h.consumedBound ?_ candidateChanged rest
    rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide : 40 + 4 ≤ 72) (by decide)]
    exact h.saved.saved 40 (by decide)
  refine ⟨context, ⟨?_, ?_⟩, changed, rest.mono (by simp [roundClobbers])⟩
  · rw [rest.sp]
    exact h.saved.space.congr rest.wr
  · intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide) (by decide)]
    all_goals first | rfl | exact h.saved.saved _ (by decide)

end VG.Proof.Ffdh.Arm.ParameterCandidate
