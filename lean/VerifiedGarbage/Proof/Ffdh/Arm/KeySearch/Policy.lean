module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.TerminalMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Terminal
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds

/-! Native 32-bit writes encode the shared four-u64 search policy exactly. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

theorem KeyLive.policy {p : KeyPublic} {original s : State} {used keys scalars request : Nat}
    (h : KeyLive p original used keys scalars s) (fits : request < 2 ^ 32)
    (low : lowWord s.mem p.control 3 = BitVec.ofNat 32 request)
    (high : s.mem.readW (off (State.addr p.control) 28) 32 = 0) :
    Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
      [BitVec.ofNat 64 keys, BitVec.ofNat 64 scalars, BitVec.ofNat 64 p.len, BitVec.ofNat 64 request] := by
  have w0 := packedWord s.mem p.control 0 keys (by have := h.keys_le; omega)
    (h.header (by simp [KeyPublic.headers])) (h.high 0 (by decide))
  have w1 := packedWord s.mem p.control 1 scalars (by have := h.scalars_le; omega)
    (h.header (by simp [KeyPublic.headers])) (h.high 1 (by decide))
  have w2 := packedWord s.mem p.control 2 p.len (by have := h.input.bounds.maxLength; omega)
    (h.header (by simp [KeyPublic.headers])) (h.high 2 (by decide))
  have w3 := packedWord s.mem p.control 3 request fits low high
  change [s.mem.readW (off (State.addr p.control) 0) 64,
    s.mem.readW (off (State.addr p.control) 8) 64,
    s.mem.readW (off (State.addr p.control) 16) 64,
    s.mem.readW (off (State.addr p.control) 24) 64] = _
  rw [w0, w1, w2, w3]

theorem KeyLive.terminal_fields {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : BitVec 32) :
    Slots (terminalMem s.mem p.control status) p.control (p.headers used 0 0) := by
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [terminalMem_low _ _ _ _ (headerIndices_bound hj), h.field hj]
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [KeyPublic.field]

theorem KeyLive.terminal {p : KeyPublic} {original s : State} {used keys scalars status : Nat}
    (h : KeyLive p original used keys scalars s) (bound : status = 1 ∨ status = 3) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal status)) s fun t =>
      KeyLive p original used 0 0 t ∧ lowWord t.mem p.control 14 = BitVec.ofNat 32 status ∧
        lowWord t.mem p.control 3 = 0 ∧ t.mem.readW (off (State.addr p.control) 28) 32 = 0 ∧
        Frame [rControl p] s.mem t.mem := by
  refine WP.mono (terminal_ok s h.controller bound) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact terminalMem_frame _ _ _
  refine ⟨h.after_control rest (by decide) frame h.used_le (by decide) (by decide) ?_ ?_, ?_, ?_, ?_, frame⟩
  · rw [mem]; exact h.terminal_fields _
  · intro j hj
    rw [mem, terminalMem_high _ _ _ j (by omega), ite_eq_right (by omega : j ≠ 3)]
    exact h.high j hj
  · rw [mem, terminalMem_low _ _ _ 14 (by decide)]
    rfl
  · rw [mem, terminalMem_low _ _ _ 3 (by decide)]
    rfl
  · change t.mem.readW (off (State.addr p.control) (8 * 3 + 4)) 32 = 0
    rw [mem, terminalMem_high _ _ _ 3 (by decide)]
    rfl

theorem KeyLive.request_fields {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Slots (requestMem s.mem p.control) p.control (p.headers used keys scalars) := by
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [requestMem_low _ _ _ (headerIndices_bound hj), h.field hj]
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

theorem KeyLive.request_block {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r10 2, .mov .r11 (.imm 0),
      VG.Impl.Ffdh.Arm.KeySearch.stf .r10 3, .str .r11 .r4 28,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r11 14]) s fun t =>
      KeyLive p original used keys scalars t ∧ lowWord t.mem p.control 14 = 0 ∧
        lowWord t.mem p.control 3 = BitVec.ofNat 32 p.len ∧
        t.mem.readW (off (State.addr p.control) 28) 32 = 0 := by
  refine WP.mono (requestBlock_ok s h.controller) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact requestMem_frame _ _
  refine ⟨h.after_control rest (by decide) frame h.used_le h.keys_le h.scalars_le ?_ ?_, ?_, ?_, ?_⟩
  · rw [mem]; exact h.request_fields
  · intro j hj
    rw [mem, requestMem_high _ _ j (by omega), ite_eq_right (by omega : j ≠ 3)]
    exact h.high j hj
  · rw [mem, requestMem_low _ _ 14 (by decide)]
    rfl
  · rw [mem, requestMem_low _ _ 3 (by decide)]
    simpa using h.header (j := 2) (by simp [KeyPublic.headers])
  · change t.mem.readW (off (State.addr p.control) (8 * 3 + 4)) 32 = 0
    rw [mem, requestMem_high _ _ 3 (by decide)]
    rfl

end VG.Proof.Ffdh.Arm.KeySearch
