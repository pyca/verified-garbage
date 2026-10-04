import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes

/-!
# Short Weierstrass curves on AArch64: masks of zero

`zeroMask n a` sets `x2` to all ones iff the `n`-word number at `a` is zero
(`zeroMask_ok`): the `orr` of its words (`ors_ok`), and whether that is below
one (`isZeroMask_ok`), by the borrow of a subtraction as a mask (`sbcMask2_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut)

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

/-- The `orr`s of `nonzero`. -/
theorem ors_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} (ha8 : a % 8 = 0) :
    ∀ k, a + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).flatMap fun j =>
        [ld .x2 (a + 8 * (j + 1)), .logic .orr .x .x1 .x1 .x2])) s fun s' =>
      (s'.gpr .x1 = 0 ↔ s.gpr .x1 = 0 ∧ ∀ j < k, word s.mem base (a + 8 * (j + 1)) = 0) ∧
      Keeps [.x1, .x2] s s'
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ors_ok hs ha8 k (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := a + 8 * (k + 1)) (by omega) (by omega) .x2) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', or_eq_zero, l₂,
      k₂.gpr .x1 (by decide), e₁, k₁.mem]
    refine ⟨⟨fun ⟨⟨h₀, h⟩, hw⟩ => ⟨h₀, fun j hj => ?_⟩, fun ⟨h₀, h⟩ => ⟨⟨h₀, fun j hj => h j (by omega)⟩,
      h k (by omega)⟩⟩, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega
        exact hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₂.gpr r (by simpa using hr.2), k₁.gpr r (by simpa using hr)]
    · rw [RegUpd.mem_write, k₂.mem, k₁.mem]
    · rw [RegUpd.rd_write, k₂.rd, k₁.rd]
    · rw [RegUpd.wr_write, k₂.wr, k₁.wr]
    · rw [RegUpd.sp_write, k₂.sp, k₁.sp]

/-- The borrow out of `x - y - b`, the complement of the carry. -/
theorem not_carryOut (x y : BitVec 64) (c : Bool) :
    (!Word64.carryOut x (~~~y) c) = decide (x.toNat < y.toNat + (!c).toNat) := by
  have h := sub_borrow x y c
  have := (Word64.addCarry x (~~~y) c).isLt
  have := x.isLt
  generalize Word64.carryOut x (~~~y) c = co at h ⊢
  cases co <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] at h ⊢
  · exact (decide_eq_true (by omega)).symm
  · exact (decide_eq_false (by omega)).symm

/-- `x2` is the mask of a borrow. -/
theorem sbcMask2_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbc .x .x2 .x7 .x7]) s fun s' =>
      s'.gpr .x2 = mask ((!s.c) = true) ∧ Keeps [.x2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨by cases s.c <;> decide, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem movz_ok (s : State) (r : Reg) (v : BitVec 16) :
    WP isa (.block [.movz .x r v 0]) s fun s' => s'.gpr r = v.setWidth 64 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by simp, fun r' hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x2` is all ones iff `x1 = 0`, with `x7 = 0`, through `x5` and `x16`. -/
theorem isZeroMask_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block isZeroMask) s fun s' =>
      s'.gpr .x2 = mask (s.gpr .x1 = 0) ∧ Keeps [.x2, .x5, .x16] s s' := by
  rw [isZeroMask, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok s .x5 1) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₁ .x16 .x1 .x5 true (c := true) rfl) fun s₂ ⟨_, c₂, k₂⟩ => ?_
  refine WP.mono (sbcMask2_ok s₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]))
    fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [e₃, c₂, not_carryOut, e₁, k₁.gpr .x1 (by decide)]
  have h1 : ((1 : BitVec 16).setWidth 64).toNat = 1 := rfl
  simp only [h1, Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.lt_one_iff, decide_eq_true_eq]
  simp only [mask]
  congr 1
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩

/-- The mask `x2` of `[a] = 0`. -/
theorem zeroMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    {n : Nat} (hn : 0 < n) (ha : a + 8 * n ≤ size) (ha8 : a % 8 = 0) :
    WP isa (.block (zeroMask n a)) s fun s' =>
      s'.gpr .x2 = mask (wordsVal s.mem base a n = 0) ∧ Keeps [.x1, .x2, .x5, .x7, .x16] s s' := by
  rw [zeroMask, List.append_assoc, WP.block_append_iff, ← List.singleton_append,
    WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  refine WP.mono (ld_ok hs₀ (d := a) (by omega) ha8 .x1) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ ha8 (n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.mem, k₀.mem] at e₂
  have hz : s₂.gpr .x1 = 0 ↔ wordsVal s.mem base a n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), z₀]
  refine WP.mono (isZeroMask_ok s₂ hz₂) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_⟩
  · rw [e₃]
    simp only [mask, hz]
  · exact (((k₀.mono (by sub_regs)).trans (k₁.mono (by sub_regs))).trans (k₂.mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))

end VG.Proof.Weierstrass.AArch64
