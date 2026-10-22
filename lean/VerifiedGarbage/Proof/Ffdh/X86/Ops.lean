module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue

/-!
# FFDH on i686: the operations on the wide slots

What the stages of the FFDH functions change: the ranges `fR` (the working
space but the saved registers' words, up to `need`). The operations of a
context (`stR len 0`: the header's first two words, the first nine wide
slots and the table) keep the FFDH slots 9 to 19 and the header from word 2
on (`opsKeep`); a number written into one wide slot keeps the others
(`slotKeep`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The ranges a stage changes: the working space up to `need`, but the saved registers' words. -/
abbrev fR (len : Nat) : List (Nat × Nat) := [(0, 32), (48, CrtRt.need len - 48)]

/-- A range within those of `fR`. -/
abbrev InF (len : Nat) (p : Nat × Nat) : Prop :=
  p.1 + p.2 ≤ 32 ∨ (48 ≤ p.1 ∧ p.1 + p.2 ≤ CrtRt.need len)

theorem fR_widen {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameR base sp ws) m m')
    (hw : ∀ p ∈ ws, InF len p) : Frame (frameR base sp (fR len)) m m' :=
  frameR_widen F fun p hp => by
    rcases hw p hp with e | e
    · exact ⟨(0, 32), by simp, by omega, by omega⟩
    · exact ⟨(48, CrtRt.need len - 48), by simp, by dsimp only; omega, by dsimp only; omega⟩

theorem fR_fit (h : In Ex base bytes len args s) : ∀ p ∈ fR len, p.1 + p.2 ≤ bytes := by
  have := h.need
  have : 48 ≤ CrtRt.need len := by simp only [CrtRt.need, numBase]; omega
  intro p hp
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> omega

theorem fR_of_outside (h : In Ex base bytes len args s) {sp : BitVec 32} {a n : Nat} {m m' : Mem}
    (O : Outside base a n m m') (hw : InF len (a, n)) : Frame (frameR base sp (fR len)) m m' := by
  have := fR_fit h
  have bl := h.bytes_lt
  have : a + n ≤ bytes := by
    rcases hw with e | e
    · have := this (0, 32) (by simp); dsimp only at *; omega
    · have := this (48, CrtRt.need len - 48) (by simp); dsimp only at *; omega
  exact fR_widen (frameR_of_outside O (by omega) (List.mem_singleton_self _))
    fun p hp => by rw [List.mem_singleton.mp hp]; exact hw

/-- The ranges of the operations of a context, within `fR`. -/
theorem stR_inF (h : In Ex base bytes len args s) : ∀ p ∈ stR len 0, InF len p := by
  have T := h.table_fit .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega
  have e28 : lo len (.slot .wide 28) = numBase + 28 * st len .wide := rfl
  have := h.slot_fit .wide (j := 27) (by decide)
  intro p hp
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> (try dsimp only) <;> omega

/-- A wide slot from 9 to 19. -/
theorem hi_fit {j : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19) :
    lo len (.slot .wide 9) ≤ lo len (.slot .wide j) ∧
      lo len (.slot .wide j) + st len .wide ≤ lo len (.slot .wide 20) := by
  have e : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) hj9
  have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 20 by omega)
  rw [Nat.succ_mul] at this
  omega

/-- The operations of a context keep the wide slots 9 to 19 and the header's words from 8 on. -/
theorem opsKeep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {d k : Nat}
    (hd : (lo len (.slot .wide 9) ≤ d ∧ d + 4 * k ≤ lo len (.slot .wide 20)) ∨ (8 ≤ d ∧ d + 4 * k ≤ numBase)) :
    val32 m' base d k = val32 m base d k := by
  have T := h.table_fit .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (stR_fit h (by decide))
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The value of a wide slot from 9 to 19 after the operations of a context. -/
theorem opsKeep_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {j : Nat} (hj9 : 9 ≤ j)
    (hj : j ≤ 19) : sv m' base len .wide j = sv m base len .wide j := by
  have := hi_fit (len := len) hj9 hj
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  exact opsKeep h F R (.inl ⟨this.1, by omega⟩)

/-- A header word from 8 on after the operations of a context. -/
theorem opsKeep_w32 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 4 ≤ numBase) : w32 m' base d = w32 m base d := by
  rw [← w32_val32_one, ← w32_val32_one]
  exact opsKeep h F R (.inr ⟨hd, by omega⟩)

/-- A number written into one wide slot keeps another. -/
theorem slotKeep (h : In Ex base bytes len args s) {m m' : Mem} {a b : Nat} (hb : b ≤ 19)
    (hab : a ≠ b) (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') :
    sv m' base len .wide b = sv m base len .wide b := by
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  exact wide_keep h hb hab (by omega) (by omega) O

/-- A number written into a wide slot keeps the header. -/
theorem slotKeep_w32 (h : In Ex base bytes len args s) {m m' : Mem} {a d : Nat}
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') (hd : d + 4 ≤ numBase) :
    w32 m' base d = w32 m base d := by
  have e : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  exact O.w32 (.inl (by omega)) (by omega)

/-- A wide slot written, within `fR`. -/
theorem slot_inF {a n : Nat} (ha : a ≤ 27) (hn : n ≤ st len .wide) :
    InF len (lo len (.slot .wide a), n) := by
  have e : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ 28 by omega)
  rw [Nat.succ_mul] at this
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  exact .inr ⟨by omega, by omega⟩

end VG.Proof.Ffdh.X86
