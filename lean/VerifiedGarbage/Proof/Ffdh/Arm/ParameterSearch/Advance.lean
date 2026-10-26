module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.RejectHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CounterMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Util.CompileInductive

/-! Rejection advances the live entropy suffix and decrements the entire native retry counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord writeLow writeLow_frame lowWord_writeLow lowValue)

theorem SearchLive.reject_head {p : SearchParams} {used remaining count : Nat} {s : State}
    (h : SearchLive p used remaining s) (bound : count ≤ p.c.bytes.length - used)
    (consumed : lowWord s.mem p.control 14 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.rejectHead) s fun t =>
      SearchLive p (used + count) remaining t ∧ Rest [.r9, .r10, .r11, .r12] s t := by
  have fieldsBound : ∀ e ∈ rejectFields p used count, e.1 < 16 := by simp [rejectFields]
  refine WP.mono (rejectHead_ok h bound consumed) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact writeLow_frame _ _ _ fieldsBound
  refine ⟨?_, rest⟩
  refine SearchLive.after_control (nextUsed := used + count) (nextRemaining := remaining)
    h (by decide) frame rest (by have := h.usedBound; omega) h.remainingBound ?_ ?_ ?_ ?_
  · have same := fields_word s.mem p.control (rejectFields p used count) fieldsBound
      (j := 0) (by decide) (by simp [rejectFields])
    have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
    rw [show 8 * 0 = 0 from rfl, address] at same
    rw [mem, same]
    exact h.counter
  · rw [mem, fields_word _ _ _ fieldsBound (j := 1) (by decide) (by simp [rejectFields])]
    exact h.width
  · rw [mem, fields_word _ _ _ fieldsBound (j := 2) (by decide) (by simp [rejectFields])]
    exact h.entropy
  · intro j member
    have hj : j < 16 := by
      simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    rw [mem, lowWord_writeLow _ _ _ fieldsBound j hj, h.saved j member]
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [rejectFields, lowValue, searchValues]

theorem SearchLive.decrement {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrement) s fun t =>
      SearchLive p used (remaining - 1) t ∧ Rest [.r9, .r10, .r12] s t := by
  refine WP.mono (decrement_ok s h.buffers.controller positive h.remaining_bound h.counter) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact counter_store_frame _ _ _
  refine ⟨?_, rest⟩
  refine SearchLive.after_control (nextUsed := used) (nextRemaining := remaining - 1)
    h (by decide) frame rest h.usedBound (by have := h.remainingBound; omega) ?_ ?_ ?_ ?_
  · rw [mem, Mem.readW_writeW_self64]
  · rw [mem, counter_store_word _ _ _ (j := 1) (by decide) (by decide)]
    exact h.width
  · rw [mem, counter_store_word _ _ _ (j := 2) (by decide) (by decide)]
    exact h.entropy
  · intro j member
    have hj : 0 < j ∧ j < 16 := by
      simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    rw [mem, counter_store_low _ _ _ hj.1 hj.2]
    exact h.saved j member

end VG.Proof.Ffdh.Arm.ParameterSearch
