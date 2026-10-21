module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseSaved
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Native Montgomery and exponent preparation establish the complete witness state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem preparedWitness_ok {s : State} {p : WitnessParams} {src : BitVec 32} {k used : Nat}
    (h : PhaseInput p src k used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      WitnessState p used 0 t ∧
      Frame [⟨State.addr p.base, 8 * p.capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have bounds : ∀ d ∈ witnessSlots, d + 4 ≤ 60 := by
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  refine WP.mono (phasePrepared_saved_ok h.preparation h.space h.saved bounds h.stackScratch) ?_
  rintro t ⟨data, saved, changed, rest⟩
  rw [h.modulus, ← h.words] at data
  refine ⟨⟨data, h.preparation.workspace.congr rest.wr, saved, ?_, ?_, ?_, h.bitsExact, h.bitsPositive,
    h.bitsBound, h.bitsFit, h.checksPositive, h.checksBound, h.usedBound, Nat.zero_le _,
    h.tapeCount, h.tapeFits, ?_, h.tapeScratch, ?_, ?_, ?_⟩, changed, rest⟩
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · rw [rest.sp]; exact h.tapeStack
  · rw [rest.sp]; exact h.tapeBelow
  · refine (rsa_bytes_frame changed (by have := h.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.tapeScratch
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate
