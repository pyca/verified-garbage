import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# ECDSA on AArch64: the masks of the checks, and the flag

The checks of `Impl/Ecdsa/AArch64.lean` as masks, all ones or zero:
`nonzero a` sets `x2` to all ones iff `[a] ≠ 0` (`nonzero_ok`), `ltN a` sets
`x2` to all ones iff `[a] < [MN]` (`ltN_ok`), and `andFlag` ands `x2` into
the flag word (`andFlag_ok`); so `checkRange a` ands the mask of
`0 < [a] < [MN]` into the flag (`checkRange_ok`) and `checkNonzero a` the mask
of `[a] ≠ 0` (`checkNonzero_ok`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut)

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

/-! ## Nonzero -/

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

/-- `x2` is all ones iff `x1 ≠ 0`, with `x7 = 0`, through `x16`. -/
theorem nzMask_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.subs .x .x16 .x7 .x1, .sbc .x .x2 .x7 .x7]) s fun s' =>
      s'.gpr .x2 = mask (s.gpr .x1 ≠ 0) ∧ Keeps [.x2, .x16] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · dsimp only [Size.bits]
    have hn : (~~~(s.gpr .x1)).toNat = 2 ^ 64 - 1 - (s.gpr .x1).toNat := BitVec.toNat_not
    have := (s.gpr .x1).isLt
    rw [hn, show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Bool.toNat_true]
    by_cases h : s.gpr .x1 = 0
    · have h' : (s.gpr .x1).toNat = 0 := by rw [h]; rfl
      rw [decide_eq_true (by omega)]
      simp only [mask, h, ne_eq, not_true_eq_false, ite_false]
      decide
    · have h' : (s.gpr .x1).toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
      rw [decide_eq_false (by omega)]
      simp only [mask, h, ne_eq, not_false_eq_true, ite_true]
      decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ite_false]

/-- `x2` is all ones iff `[a] ≠ 0`; `x1`, `x7` and `x16` change too. -/
theorem nonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (ha8 : a % 8 = 0) :
    WP isa (.block (c.nonzero a)) s fun s' =>
      s'.gpr .x2 = mask (wordsVal s.mem base a c.n ≠ 0) ∧ Keeps [.x1, .x2, .x7, .x16] s s' := by
  rw [Cfg.nonzero, List.append_assoc, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  refine WP.mono (ld_ok hs₀ (d := a) (by omega) ha8 .x1) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ ha8 (c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.mem, k₀.mem] at e₂
  have hz : s₂.gpr .x1 = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), z₀]
  refine WP.mono (nzMask_ok s₂ hz₂) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_⟩
  · rw [e₃]
    simp only [mask, ne_eq, hz]
  · exact (((k₀.mono (by sub_regs)).trans (k₁.mono (by sub_regs))).trans (k₂.mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))

/-! ## Less than the order -/

/-- One word of the comparison of `[a]` with `[m]`. -/
def ltStep (a m j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), ld .x2 (m + 8 * j), if j = 0 then .subs .x .x16 .x1 .x2 else .sbcs .x .x16 .x1 .x2]

theorem ltN_eq (c : Cfg) (a : Nat) :
    c.ltN a = zero7 :: ((List.range c.n).flatMap (ltStep a (c.sl MN)) ++ ([.sbc .x .x2 .x7 .x7] : List Instr)) :=
  rfl

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

theorem ltStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m j : Nat}
    (first : Bool) {c : Bool} (hc : (if first then true else s.c) = c)
    (hcode : ltStep a m j = [ld .x1 (a + 8 * j), ld .x2 (m + 8 * j),
      if first then .subs .x .x16 .x1 .x2 else .sbcs .x .x16 .x1 .x2])
    (ha : a + 8 * j + 8 ≤ size) (hm : m + 8 * j + 8 ≤ size) (ha8 : a % 8 = 0) (hm8 : m % 8 = 0) :
    WP isa (.block (ltStep a m j)) s fun s' =>
      (!s'.c) = decide ((word s.mem base (a + 8 * j)).toNat < (word s.mem base (m + 8 * j)).toNat + (!c).toNat) ∧
      Keeps [.x1, .x2, .x16] s s' := by
  rw [hcode, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs ha (by omega) .x1) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs₁ hm (by omega) .x2) fun s₂ ⟨l₂, k₂, c₂⟩ => ?_
  refine WP.mono (subc_ok s₂ .x16 .x1 .x2 first (c := c) (by rw [c₂, c₁, hc])) fun s₃ ⟨_, c₃, k₃⟩ => ⟨?_, ?_⟩
  · rw [c₃, not_carryOut, l₂, k₂.gpr .x1 (by decide), l₁, k₁.mem]
  · exact ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

theorem ltSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (ha8 : a % 8 = 0) (hm8 : m % 8 = 0) :
    ∀ k, a + 8 * (k + 1) ≤ size → m + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range (k + 1)).flatMap (ltStep a m))) s fun s' =>
      (!s'.c) = decide (wordsVal s.mem base a (k + 1) < wordsVal s.mem base m (k + 1)) ∧
      Keeps [.x1, .x2, .x16] s s'
  | 0, ha, hm => by
    rw [show (List.range (0 + 1)).flatMap (ltStep a m) = ltStep a m 0 from rfl]
    refine WP.mono (ltStep_ok hs true (c := true) rfl rfl (by omega) (by omega) ha8 hm8) fun s' ⟨c', k'⟩ => ⟨?_, k'⟩
    rw [c']
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Bool.not_true, Bool.toNat_false]
    rfl
  | k + 1, ha, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ltSteps_ok hs ha8 hm8 k (by omega) (by omega)) fun s₁ ⟨c₁, k₁⟩ => ?_
    refine WP.mono (ltStep_ok (hs.of_keeps k₁ (by decide)) false (c := s₁.c) rfl rfl (by omega) (by omega) ha8 hm8)
      fun s₂ ⟨c₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [c₂, c₁, k₁.mem, wordsVal_succ_top s.mem base a (k + 1), wordsVal_succ_top s.mem base m (k + 1)]
    exact decide_eq_decide.mpr (lt_top (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)).symm

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

/-- `x2` is all ones iff `[a] < [MN]`; `x1`, `x7` and `x16` change too. -/
theorem ltN_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) (ha8 : a % 8 = 0)
    (hm8 : c.sl MN % 8 = 0) :
    WP isa (.block (c.ltN a)) s fun s' =>
      s'.gpr .x2 = mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Keeps [.x1, .x2, .x7, .x16] s s' := by
  obtain ⟨k, hk⟩ : ∃ k, c.n = k + 1 := ⟨c.n - 1, by omega⟩
  rw [ltN_eq, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  rw [WP.block_append_iff, hk]
  rw [hk] at ha hm
  refine WP.mono (ltSteps_ok (hs.of_keeps k₀ (by decide)) ha8 hm8 k ha hm) fun s₁ ⟨c₁, k₁⟩ => ?_
  refine WP.mono (sbcMask2_ok s₁ (by rw [k₁.gpr _ (by decide), z₀])) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨?_, ((k₀.mono (by sub_regs)).trans (k₁.mono (by sub_regs))).trans (k₂.mono (by sub_regs))⟩
  rw [e₂, c₁, k₀.mem]
  simp only [mask, decide_eq_true_eq]

/-! ## The flag -/

/-- `[FLAG] &= x2`, through `x1`. -/
theorem andFlag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : c.sl FLAG + 8 ≤ size) (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block c.andFlag) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& s.gpr .x2 ∧
      KeepRegs [.x1] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Cfg.andFlag, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hf hf8 .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.logic .and .x .x1 .x1 .x2]) s₁ (fun s₂ =>
      s₂.gpr .x1 = s₁.gpr .x1 &&& s₁.gpr .x2 ∧ Keeps [.x1] s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.mono (st_ok hs₂ hf hf8 .x1) fun s₃ e₃ => ?_
  subst e₃
  have hm : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [word_writeW_self, e₂, l₁, k₁.gpr .x2 (by decide)]
  · dsimp only
    simp only [List.mem_singleton] at hr
    rw [k₂.gpr r (by simpa using hr), k₁.gpr r (by simpa using hr)]
  · dsimp only; rw [k₂.rd, k₁.rd]
  · dsimp only; rw [k₂.wr, k₁.wr]
  · dsimp only; rw [k₂.sp, k₁.sp]
  · dsimp only
    rw [hm]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size)
    (ha8 : a % 8 = 0) (hm8 : c.sl MN % 8 = 0) (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block (c.checkRange a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        mask (0 < wordsVal s.mem base a c.n ∧ wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      KeepRegs [.x1, .x2, .x4, .x7, .x16] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Cfg.checkRange, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ltN_ok c hs hn ha hm ha8 hm8) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.addImm .x .x4 .x2 0]) s₁ (fun s₂ =>
      s₂.gpr .x4 = s₁.gpr .x2 ∧ Keeps [.x4] s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (0 : Nat) < 4096 by decide,
      ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nonzero_ok c hs₂ hn ha ha8) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.logic .and .x .x2 .x2 .x4]) s₃ (fun s₄ =>
      s₄.gpr .x2 = s₃.gpr .x2 &&& s₃.gpr .x4 ∧ Keeps [.x2] s₃ s₄) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ hf hf8) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hm₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have hx4 : s₃.gpr .x4 = s₁.gpr .x2 := by rw [k₃.gpr _ (by decide), e₂]
  rw [k₂.mem, k₁.mem] at e₃
  refine ⟨?_, ?_, by rw [← hm₄]; exact O₅⟩
  · rw [e₅, hm₄, e₄, e₃, hx4, e₁, mask_and]
    simp only [Nat.pos_iff_ne_zero]
  · exact ((((Keeps.regs k₁).mono (by sub_regs)).trans ((Keeps.regs k₂).mono (by sub_regs))).trans
      ((Keeps.regs k₃).mono (by sub_regs))).trans (((Keeps.regs k₄).mono (by sub_regs)).trans
      (k₅.mono (by sub_regs)))

/-- `checkNonzero a`: the flag `&=` the mask of `[a] ≠ 0`. -/
theorem checkNonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) (ha8 : a % 8 = 0)
    (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block (c.checkNonzero a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (wordsVal s.mem base a c.n ≠ 0) ∧
      KeepRegs [.x1, .x2, .x7, .x16] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Cfg.checkNonzero, WP.block_append_iff]
  refine WP.mono (nonzero_ok c hs hn ha ha8) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_keeps k₁ (by decide)) hf hf8) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine ⟨by rw [e₂, e₁, k₁.mem], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
    by rw [← k₁.mem]; exact O₂⟩

end VG.Proof.Ecdsa.AArch64
