module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Advance
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! The retry controller consumes one scalar width per attempt, then updates
exactly the rejection budget corresponding to its returned status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem KeyLive.advance_fields {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen) :
    Slots (writeLow s.mem p.control (advanceValues s.mem p.control)) p.control
      (p.headers (used + p.len) keys scalars) := by
  have w2 := h.field (j := 2) (by simp [headerIndices])
  have w9 := h.field (j := 9) (by simp [headerIndices])
  have w10 := h.field (j := 10) (by simp [headerIndices])
  have w11 := h.field (j := 11) (by simp [headerIndices])
  have rem : BitVec.ofNat 32 (p.randLen - used) - BitVec.ofNat 32 p.len =
      BitVec.ofNat 32 (p.randLen - (used + p.len)) := by
    rw [Offset.ofNat_sub_ofNat (by omega : p.len ≤ p.randLen - used), Nat.sub_sub]
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [advanceValues]) j (headerIndices_bound hj), h.field hj]
  simp only [KeyPublic.field] at w2 w9 w10 w11
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, advanceValues, KeyPublic.field, w2, w9, w10, w11,
    BitVec.add_assoc, ← BitVec.ofNat_add, rem]

theorem KeyLive.advance {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advance) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ t.gpr .r9 = s.gpr .r0 ∧
        Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
  refine WP.mono (advance_ok s h.controller) ?_
  rintro t ⟨⟨status, mem⟩, rest⟩
  refine ⟨h.update rest (by decide) (advanceValues s.mem p.control) (by simp [advanceValues])
    mem room h.keys_le h.scalars_le ?_, status, ?_⟩
  · rw [mem]; exact h.advance_fields room
  · rw [mem]; exact writeLow_frame _ _ _ (by simp [advanceValues])

theorem KeyLive.scalar_fields {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < scalars) :
    Slots (writeLow s.mem p.control (scalarValues s.mem p.control)) p.control
      (p.headers used keys (scalars - 1)) := by
  have w1 := h.field (j := 1) (by simp [headerIndices])
  simp only [KeyPublic.field] at w1
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [scalarValues]) j (headerIndices_bound hj), h.field hj]
  have sub : BitVec.ofNat 32 scalars - 1#32 = BitVec.ofNat 32 (scalars - 1) :=
    Offset.ofNat_sub_ofNat (by omega : 1 ≤ scalars)
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, scalarValues, KeyPublic.field, w1, sub]

theorem KeyLive.reject_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < scalars) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ lowWord t.mem p.control 14 = 4 := by
  refine WP.mono (rejectedScalar_ok s h.controller) ?_
  rintro t ⟨mem, rest⟩
  refine ⟨h.update rest (by decide) (scalarValues s.mem p.control) (by simp [scalarValues])
    mem h.used_le h.keys_le (by have := h.scalars_le; omega) ?_, ?_⟩
  · rw [mem]; exact h.scalar_fields positive
  · rw [mem, lowWord_writeLow _ _ _ (by simp [scalarValues]) 14 (by decide)]
    simp [scalarValues, lowValue]

theorem KeyLive.public_fields {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < keys) :
    Slots (writeLow s.mem p.control (publicValues s.mem p.control)) p.control
      (p.headers used (keys - 1) 128) := by
  have w0 := h.field (j := 0) (by simp [headerIndices])
  simp only [KeyPublic.field] at w0
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [publicValues]) j (headerIndices_bound hj), h.field hj]
  have sub : BitVec.ofNat 32 keys - 1#32 = BitVec.ofNat 32 (keys - 1) :=
    Offset.ofNat_sub_ofNat (by omega : 1 ≤ keys)
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, publicValues, KeyPublic.field, w0, sub]

theorem KeyLive.reject_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < keys) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ lowWord t.mem p.control 14 = 4 := by
  refine WP.mono (rejectedPublic_ok s h.controller) ?_
  rintro t ⟨mem, rest⟩
  refine ⟨h.update rest (by decide) (publicValues s.mem p.control) (by simp [publicValues])
    mem h.used_le (by have := h.keys_le; omega) (by decide) ?_, ?_⟩
  · rw [mem]; exact h.public_fields positive
  · rw [mem, lowWord_writeLow _ _ _ (by simp [publicValues]) 14 (by decide)]
    simp [publicValues, lowValue]

end VG.Proof.Ffdh.Arm.KeySearch
