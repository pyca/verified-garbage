module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Request
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PolicyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block

/-! Terminal and entropy-request policy updates retain the native search's live buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem SearchLive.terminal {p : SearchParams} {used remaining status : Nat} {s : State}
    (h : SearchLive p used remaining s) (bound : status = 1 ∨ status = 3) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterSearch.terminal status)) s fun t =>
      SearchLive p used 0 t ∧ lowWord t.mem p.control 13 = BitVec.ofNat 32 status ∧
        t.mem.readW (off (State.addr p.control) 24) 64 = 0 ∧
        Frame [⟨State.addr p.control, 128⟩] s.mem t.mem ∧ Rest [.r10, .r11] s t := by
  refine WP.mono (terminal_ok s h.buffers.controller bound) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact terminalMem_frame _ _ _
  have live : SearchLive p used 0 t := by
    refine SearchLive.after_control (nextUsed := used) (nextRemaining := 0) h (by decide) frame rest h.usedBound (Nat.zero_le _) ?_ ?_ ?_ ?_
    · have address : off (State.addr p.control) (8 * 0) = State.addr p.control := by simp [off]
      rw [← address, mem, terminalMem_word _ _ _ 0 (by decide)]
      rfl
    · rw [mem, terminalMem_word _ _ _ 1 (by decide)]
      exact h.width
    · rw [mem, terminalMem_word _ _ _ 2 (by decide)]
      exact h.entropy
    · intro j member
      have bounds : j < 16 ∧ j ≠ 13 ∧ ¬ (j = 0 ∨ j = 3) := by
        simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      rw [mem, terminalMem_low _ _ _ j bounds.1, ite_eq_right bounds.2.1, ite_eq_right bounds.2.2]
      exact h.saved j member
  refine ⟨live, ?_, ?_, frame, rest⟩
  · rw [mem, terminalMem_low _ _ _ 13 (by decide)]
    rfl
  · rw [mem]
    exact terminalMem_word s.mem p.control status 3 (by decide)

theorem SearchLive.request {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.request s fun t =>
      SearchLive p used remaining t ∧ lowWord t.mem p.control 13 = 0 ∧
        t.mem.readW (off (State.addr p.control) 24) 64 =
          BitVec.ofNat 64 (Spec.Ffdh.parameterRequest p.c.bits (p.c.bytes.length - used)) ∧
        Frame [⟨State.addr p.control, 128⟩] s.mem t.mem ∧ Rest [.r9, .r10, .r11] s t := by
  let request := Spec.Ffdh.parameterRequest p.c.bits (p.c.bytes.length - used)
  have fit : request < 2 ^ 32 := Nat.lt_of_le_of_lt p.policy.request_bounds.2 p.entropy_fits
  refine WP.mono (request_ok h) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact requestMem_frame _ _ _
  have live : SearchLive p used remaining t := by
    refine SearchLive.after_control (nextUsed := used) (nextRemaining := remaining) h (by decide) frame rest h.usedBound h.remainingBound ?_ ?_ ?_ ?_
    · have address : off (State.addr p.control) (8 * 0) = State.addr p.control := by simp [off]
      rw [← address, mem, requestMem_word _ _ _ 0 (by decide) fit]
      rw [address]
      exact h.counter
    · rw [mem, requestMem_word _ _ _ 1 (by decide) fit]
      exact h.width
    · rw [mem, requestMem_word _ _ _ 2 (by decide) fit]
      exact h.entropy
    · intro j member
      have bounds : j < 16 ∧ j ≠ 13 ∧ j ≠ 3 := by
        simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      rw [mem, requestMem_low _ _ _ j bounds.1, ite_eq_right bounds.2.1, ite_eq_right bounds.2.2]
      exact h.saved j member
  refine ⟨live, ?_, ?_, frame, rest⟩
  · rw [mem, requestMem_low _ _ _ 13 (by decide)]
    rfl
  · rw [mem]
    exact requestMem_word s.mem p.control request 3 (by decide) fit

end VG.Proof.Ffdh.Arm.ParameterSearch
