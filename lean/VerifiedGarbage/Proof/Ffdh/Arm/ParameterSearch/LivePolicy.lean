module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PolicyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.RequestBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Select
/-! Terminal and entropy-request policy updates retain the native search's live buffers. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Request.lean`, which only this module imported.
section

/-! The native refill request is exactly the shared bounded doubling policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem request_ok {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.request s fun t =>
      t.mem = requestMem s.mem p.control (Spec.Ffdh.parameterRequest p.c.bits (p.c.bytes.length - used)) ∧
        Rest [.r9, .r10, .r11] s t := by
  let available := p.c.bytes.length - used
  let width := p.c.length
  let cap := Spec.Ffdh.parameterEntropy p.c.bits
  let peak := max available (256 * width)
  have widthBound := p.width_bounds
  have capBound := p.entropy_bound
  have tapeBound : p.c.bytes.length ≤ Spec.Ffdh.parameterEntropy p.c.bits := p.tapeBound
  have doubleFits : 2 * peak < 2 ^ 32 := p.policy.double_fits (by omega)
  have availableFits : available < 2 ^ 32 := by have := p.c.tapeCount; omega
  have peakFits : peak < 2 ^ 32 := by omega
  have widthFits : 256 * width < 2 ^ 32 := by dsimp only [width]; omega
  have control := h.buffers.controller
  have tape := h.saved 10 (by simp [searchSlots])
  have length := h.saved 1 (by simp [searchSlots])
  have capacity := h.saved 2 (by simp [searchSlots])
  simp only [searchValues] at tape length capacity
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.request
  rw [WP.seq_iff]
  refine WP.mono (requestHead_ok s control tape length) ?_
  rintro a ⟨⟨leftA, rightA, memA⟩, restA⟩
  refine WP.seq (WP.mono (selectNat_ok true a availableFits widthFits leftA rightA)
    fun c ⟨⟨peakC, memC⟩, restC⟩ => ?_)
  have restSC : Rest [.r9, .r10, .r11] s c :=
    (restA.mono (by simp)).trans (restC.mono (by simp))
  have memSC : c.mem = s.mem := memC.trans memA
  have controlC : Controller p.control c :=
    ⟨control.space.congr restSC.wr, (restSC.gpr .r4 (by simp)).trans control.ptr⟩
  have capC : lowWord c.mem p.control 2 = BitVec.ofNat 32 cap := by rw [memSC]; exact capacity
  rw [WP.seq_iff]
  refine WP.mono (requestDouble_ok c controlC peakC capC) ?_
  rintro d ⟨⟨leftD, rightD, memD⟩, restD⟩
  refine WP.seq (WP.mono (selectNat_ok false d doubleFits p.entropy_fits leftD rightD)
    fun f ⟨⟨requestF, memF⟩, restF⟩ => ?_)
  have restSF : Rest [.r9, .r10, .r11] s f :=
    (restSC.trans (restD.mono (by simp))).trans (restF.mono (by simp))
  have memSF : f.mem = s.mem := memF.trans (memD.trans memSC)
  have controlF : Controller p.control f :=
    ⟨control.space.congr restSF.wr, (restSF.gpr .r4 (by simp)).trans control.ptr⟩
  refine WP.mono (requestStore_ok f controlF requestF) ?_
  rintro t ⟨memT, restT⟩
  exact ⟨by rw [memT, memSF]; rfl, restSF.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

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
