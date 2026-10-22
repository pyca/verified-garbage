module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Framework.Omega

/-! # The ranges a factor's power changes

`stR len o`: the header's first two words, the first nine wide slots (both
contexts' slots), the table, and the result's wide slot `o`. Every range a
step of a power changes lies within one of them (`stR_widen`), and they
keep the key's components in the wide slots 9 to 15 and the other result
(`stR_keep`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges a factor's power into the wide slot `o` changes. -/
abbrev stR (len o : Nat) : List (Nat × Nat) :=
  [(0, 8), (numBase, 9 * st len .wide), (te len .wide 0, 16 * bc len .wide),
    (lo len (.slot .wide o), 2 * bc len .wide)]

/-- A range within another. -/
abbrev Within (p q : Nat × Nat) : Prop := q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A context's slots 0 to 8 lie within the first nine wide slots. -/
theorem ctx_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) :
    numBase ≤ lo len (.slot c j) ∧ lo len (.slot c j) + st len c ≤ numBase + 9 * st len .wide := by
  have e : lo len (.slot c j) = numBase + j * st len c := rfl
  refine ⟨by omega, ?_⟩
  cases c with
  | half =>
    have := half_in_wide h hj
    have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
    omega
  | wide =>
    have := Nat.mul_le_mul_right (st len .wide) hj
    have e' : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    omega

theorem bc_le_wide (len : Nat) (c : Ctx) : bc len c ≤ bc len .wide := by
  have hb := bc_half_le' len
  have := bc_dvd len .half
  cases c <;> omega

/-- The context's ranges from its slot 1 on, within the first nine wide slots. -/
theorem slot1_in (h : In Ex base bytes len args s) (c : Ctx) :
    Within (lo len (.slot c 1), 3 * bc len c + 56) (numBase, 9 * st len .wide) := by
  have a := ctx_in h c (j := 1) (by decide)
  have b := ctx_in h c (j := 2) (by decide)
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e2 : lo len (.slot c 2) = numBase + 2 * st len c := rfl
  have est : st len c = 2 * bc len c + 32 := rfl
  exact ⟨a.1, by dsimp only; omega⟩

theorem slot_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) :
    Within (lo len (.slot c j), bc len c) (numBase, 9 * st len .wide) := by
  have a := ctx_in h c hj
  have est : st len c = 2 * bc len c + 32 := rfl
  exact ⟨a.1, by dsimp only; omega⟩

theorem table_in (c : Ctx) (len : Nat) :
    Within (te len c 0, 16 * bc len c) (te len .wide 0, 16 * bc len .wide) := by
  have := bc_le_wide len c
  have e : te len c 0 = te len .wide 0 := by simp [te]
  exact ⟨by rw [e], by dsimp only; rw [e]; omega⟩

/-- Every range of `ws` within one of `stR`. -/
abbrev InSt (len o : Nat) (ws : List (Nat × Nat)) : Prop := ∀ p ∈ ws, ∃ q ∈ stR len o, Within p q

theorem stR_widen {sp : BitVec 32} {o : Nat} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hw : InSt len o ws) : Frame (frameR base sp (stR len o)) m m' :=
  frameR_widen F hw

theorem prepR_in (h : In Ex base bytes len args s) (c : Ctx) (o : Nat) : InSt len o (prepR len c) := by
  intro p hp
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  have s1 := slot1_in h c
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), by simp, by simp only [invOff]; omega, by simp only [invOff]; omega⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, s1.1, by have := s1.2; dsimp only at *; have := bc_ge h.lower' c; omega⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩

theorem mulR_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) (o : Nat) :
    InSt len o (mulR len c j) := by
  intro p hp
  simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨_, by simp, slot_in h c hj⟩
  · exact ⟨_, by simp, slot1_in h c⟩

theorem pwR_in (h : In Ex base bytes len args s) (c : Ctx) (o : Nat) : InSt len o (pwR len c) := by
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), by simp, by simp only [winOff]; omega, by simp only [winOff]; omega⟩
  · exact ⟨_, by simp, slot1_in h c⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, table_in c len⟩

theorem stR_fit (h : In Ex base bytes len args s) {o : Nat} (ho : o ≤ 19) :
    ∀ q ∈ stR len o, q.1 + q.2 ≤ bytes := by
  have T := h.table_fit .wide
  have W := h.wide_fit ho
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- A change within one range of `stR`. -/
theorem stR_of_outside (h : In Ex base bytes len args s) {sp : BitVec 32} {o a n : Nat} (ho : o ≤ 19) {m m' : Mem}
    (O : Outside base a n m m') (hq : ∃ q ∈ stR len o, Within (a, n) q) :
    Frame (frameR base sp (stR len o)) m m' := by
  obtain ⟨q, hq, w⟩ := hq
  have := stR_fit h ho q hq
  have bl := h.bytes_lt
  have w2 : a + n ≤ q.1 + q.2 := w.2
  refine stR_widen (ws := [(a, n)]) (frameR_of_outside O (by omega) (by simp)) ?_
  intro p hp
  rw [List.mem_singleton.mp hp]
  exact ⟨q, hq, w⟩

/-- A power keeps the key's components and the other result: everything from wide slot 9 on but
the result's slot and the table. -/
theorem stR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17)
    {m m' : Mem} (F : Frame (frameR base sp (stR len o)) m m') (R : CallRoom sp base bytes) {d k : Nat}
    (hd : lo len (.slot .wide 9) ≤ d) (hk : d + 4 * k ≤ lo len (.slot .wide 18))
    (hdo : d + 4 * k ≤ lo len (.slot .wide o) ∨ lo len (.slot .wide o) + 2 * bc len .wide ≤ d) :
    val32 m' base d k = val32 m base d k := by
  have W := h.wide_fit (j := 18) (by decide)
  have T := h.table_fit .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have W19 := h.wide_fit (j := 19) (by decide)
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (stR_fit h (by omega))
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> (try dsimp only)
  · have nb : numBase = 3336 := rfl
    omega
  · omega
  · omega
  · exact hdo

end

end VG.Proof.Bignum.X86.CrtRt
