module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Terminal
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller

/-! Packed controller-word effects of finishing or requesting entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

theorem highStore_low (m : Mem) (base : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    lowWord (m.writeW (off (State.addr base) (8 * i + 4)) v) base j = lowWord m base j :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem highStore_high (m : Mem) (base : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    (m.writeW (off (State.addr base) (8 * i + 4)) v).readW (off (State.addr base) (8 * j + 4)) 32 =
      if j = i then v else m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  by_cases eq : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right eq]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem terminalMem_low (m : Mem) (base : BitVec 32) (status : BitVec 32) (j : Nat) (hj : j < 16) :
    lowWord (terminalMem m base status) base j =
      if j = 14 then status else if j = 0 ∨ j = 1 ∨ j = 3 then 0 else lowWord m base j := by
  unfold terminalMem
  rw [lowWord_store (i := 14) _ _ _ (by decide) hj,
    highStore_low (i := 3) _ _ _ (by decide) hj,
    lowWord_writeLow _ _ _ (by simp) j hj]
  simp only [lowValue, List.foldl_cons, List.foldl_nil]
  by_cases h14 : j = 14
  · simp only [h14, ite_true]
  · by_cases h0 : j = 0
    · simp [h0]
    · by_cases h1 : j = 1
      · simp [h1]
      · by_cases h3 : j = 3 <;> simp [h14, h0, h1, h3]

theorem terminalMem_high (m : Mem) (base : BitVec 32) (status : BitVec 32) (j : Nat) (hj : j < 16) :
    (terminalMem m base status).readW (off (State.addr base) (8 * j + 4)) 32 =
      if j = 3 then 0 else m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  unfold terminalMem
  rw [highWord_store (i := 14) _ _ _ (by decide) (by omega),
    highStore_high (i := 3) _ _ _ (by decide) (by omega),
    highWord_writeLow _ _ _ (by simp) j (by omega)]
  rfl

theorem terminalMem_frame (m : Mem) (base : BitVec 32) (status : BitVec 32) :
    Frame [⟨State.addr base, 128⟩] m (terminalMem m base status) := by
  unfold terminalMem
  exact ((writeLow_frame _ _ _ (by simp)).writeW (by simp) _
    (Offset.contains_base _ (by decide : 28 + 4 ≤ 128) (by decide))).writeW (by simp) _
      (Offset.contains_base _ (by decide : 112 + 4 ≤ 128) (by decide))

theorem requestMem_low (m : Mem) (base : BitVec 32) (j : Nat) (hj : j < 16) :
    lowWord (requestMem m base) base j =
      if j = 14 then 0 else if j = 3 then lowWord m base 2 else lowWord m base j := by
  unfold requestMem
  rw [lowWord_store (i := 14) _ _ _ (by decide) hj,
    highStore_low (i := 3) _ _ _ (by decide) hj,
    lowWord_writeLow _ _ _ (by simp) j hj]
  rfl

theorem requestMem_high (m : Mem) (base : BitVec 32) (j : Nat) (hj : j < 16) :
    (requestMem m base).readW (off (State.addr base) (8 * j + 4)) 32 =
      if j = 3 then 0 else m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  unfold requestMem
  rw [highWord_store (i := 14) _ _ _ (by decide) (by omega),
    highStore_high (i := 3) _ _ _ (by decide) (by omega),
    highWord_writeLow _ _ _ (by simp) j (by omega)]
  rfl

theorem requestMem_frame (m : Mem) (base : BitVec 32) :
    Frame [⟨State.addr base, 128⟩] m (requestMem m base) := by
  unfold requestMem
  exact ((writeLow_frame _ _ _ (by simp)).writeW (by simp) _
    (Offset.contains_base _ (by decide : 28 + 4 ≤ 128) (by decide))).writeW (by simp) _
      (Offset.contains_base _ (by decide : 112 + 4 ≤ 128) (by decide))

theorem CachedSlots.terminal {sampling : GenerationPolicy} {p : KeyPublic sampling} {m : Mem}
    (h : CachedSlots p m) (status : BitVec 32) : CachedSlots p (terminalMem m p.control status) := by
  intro cached
  obtain ⟨ptr, words⟩ := h cached
  constructor
  · change lowWord (terminalMem m p.control status) p.control 4 = p.context
    rw [terminalMem_low _ _ _ 4 (by decide)]
    exact ptr
  · change (terminalMem m p.control status).readW (off (State.addr p.control) (8 * 4 + 4)) 32 = _
    rw [terminalMem_high _ _ _ 4 (by decide)]
    exact words

theorem CachedSlots.request {sampling : GenerationPolicy} {p : KeyPublic sampling} {m : Mem}
    (h : CachedSlots p m) : CachedSlots p (requestMem m p.control) := by
  intro cached
  obtain ⟨ptr, words⟩ := h cached
  constructor
  · change lowWord (requestMem m p.control) p.control 4 = p.context
    rw [requestMem_low _ _ 4 (by decide)]
    exact ptr
  · change (requestMem m p.control).readW (off (State.addr p.control) (8 * 4 + 4)) 32 = _
    rw [requestMem_high _ _ 4 (by decide)]
    exact words

end VG.Proof.Ffdh.Arm.KeySearch
