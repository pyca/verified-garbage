import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Impl.Weierstrass.AArch64.Chain

/-!
# Short Weierstrass curves on AArch64: powers by sliding windows

`ChainCfg.pow P` leaves `[acc]` reading (in Montgomery form) as `[base]^e` for
an exponent `e` whose chain the configuration holds (`ChainOk`): the table
holds `B^(2 i + 1)` and `B²` (`table_ok`), each step takes `B^v` to
`B^(v 2^s + d)` (`step_ok`: squarings by a counted loop, `squares_ok`, and a
multiplication by the table), so the steps take `B^first` to `B^e`
(`chainPow_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- What a power by a chain writes: the result, the table and the modulus's
temporary area. -/
def chainW (P : ChainCfg) : List (Nat × Nat) :=
  [(P.acc, 8 * P.M.n), (P.tbl, 9 * (8 * P.M.n)), (P.M.tmp, 8 * P.M.n)]

/-- The chain's slots are in the working space, aligned and apart, and the
modulus and its temporary area apart from them. -/
structure ChainLay (P : ChainCfg) (size : Nat) : Prop where
  n0 : 0 < P.M.n
  acc : P.acc + 8 * P.M.n ≤ size
  base : P.base + 8 * P.M.n ≤ size
  tbl : P.tbl + 9 * (8 * P.M.n) ≤ size
  acc8 : P.acc % 8 = 0
  base8 : P.base % 8 = 0
  tbl8 : P.tbl % 8 = 0
  mod : ModA P.M
  acc_base : P.acc + 8 * P.M.n ≤ P.base ∨ P.base + 8 * P.M.n ≤ P.acc
  acc_tbl : P.acc + 8 * P.M.n ≤ P.tbl ∨ P.tbl + 9 * (8 * P.M.n) ≤ P.acc
  base_tbl : P.base + 8 * P.M.n ≤ P.tbl ∨ P.tbl + 9 * (8 * P.M.n) ≤ P.base
  acc_tmp : P.acc + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.acc
  base_tmp : P.base + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.base
  tbl_tmp : P.tbl + 9 * (8 * P.M.n) ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.tbl
  mo_w : ∀ w ∈ chainW P, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo
  base_mo : P.base + 8 * P.M.n ≤ P.M.mo ∨ P.M.mo + 8 * P.M.n ≤ P.base

/-- The chain is the exponent's: an odd first window up to 15, from one to
`2^16 - 1` steps (the loop's count, in a `movz`), each of `1 … 2^16 - 1`
squarings and an odd digit up to 15, and the value `e`. -/
structure ChainOk (P : ChainCfg) (e : Nat) : Prop where
  first : P.first % 2 = 1 ∧ P.first ≤ 15
  len : 1 ≤ P.steps.length ∧ P.steps.length < 2 ^ 16
  steps : ∀ st ∈ P.steps, 1 ≤ st.1 ∧ st.1 < 2 ^ 16 ∧ st.2 % 2 = 1 ∧ st.2 ≤ 15
  val : chainVal P.first P.steps = e

/-- `ChainOk`, as a computation (`decide +kernel` evaluates it for a curve). -/
def chainCheck (first : Nat) (steps : List (Nat × Nat)) (e : Nat) : Bool :=
  first % 2 == 1 && decide (first ≤ 15) && decide (1 ≤ steps.length) &&
    decide (steps.length < 2 ^ 16) &&
    steps.all (fun st => decide (1 ≤ st.1) && decide (st.1 < 2 ^ 16) && st.2 % 2 == 1 &&
      decide (st.2 ≤ 15)) &&
    chainVal first steps == e

theorem ChainOk.of_check {P : ChainCfg} {e : Nat} (h : chainCheck P.first P.steps e = true) :
    ChainOk P e := by
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun st hst => by
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h5 st hst; exact ⟨a, b, c, d⟩, h6⟩

/-- Slot `i ≤ 8` of the table, in its area. -/
theorem slot_le (P : ChainCfg) {i : Nat} (hi : i ≤ 8) :
    P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) := by
  have := Nat.mul_le_mul_left (8 * P.M.n) hi
  simp only [ChainCfg.slot]
  omega

theorem slot_apart (P : ChainCfg) {i j : Nat} (h : i ≠ j) :
    P.slot i + 8 * P.M.n ≤ P.slot j ∨ P.slot j + 8 * P.M.n ≤ P.slot i := by
  simp only [ChainCfg.slot]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * P.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega
  · right; have := Nat.mul_le_mul_left (8 * P.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega

theorem slot_mod8 (P : ChainCfg) (h : P.tbl % 8 = 0) (i : Nat) : P.slot i % 8 = 0 := by
  simp only [ChainCfg.slot]; rw [Nat.mul_assoc]; omega

/-- An operation's writes, within what the chain writes. -/
theorem op_cover {P : ChainCfg} {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n))) :
    ∀ w ∈ [(o, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)], ∃ w' ∈ chainW P, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rcases ho with rfl | ho
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ho.1, ho.2⟩
  · exact ⟨_, by simp [chainW], Nat.le_refl _, Nat.le_refl _⟩

/-- What holds throughout the power, from `s₀`. -/
structure ChainSt (P : ChainCfg) (base : Addr) (size m : Nat) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob P.M.n) s₀ s
  unch : Unch base (chainW P) s₀.mem s.mem
  mod : ModOkA P.M size m s.mem base

/-- An operation writing the result or a table slot. -/
theorem ChainSt.op {P : ChainCfg} {base : Addr} {size m : Nat} (hL : ChainLay P size)
    {s₀ s s' : State} (h : ChainSt P base size m s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n))) (hk : OpKeep P.M base o s s') :
    ChainSt P base size m s₀ s' := by
  have U := hk.unch.cover (op_cover ho)
  refine ⟨hk.scr h.scr, h.keep.trans ⟨fun r hr => hk.gpr r fun h => hr (List.mem_cons_of_mem _ h),
    hk.rd, hk.wr, hk.sp⟩, (h.unch.trans U).cover fun w hw => ?_, h.mod.unch U (hL.mo_w) h.scr.nowrap⟩
  rcases List.mem_append.mp hw with hw | hw <;> exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩

/-- `B`, what the base reads as. -/
abbrev bv (P : ChainCfg) (base : Addr) (m : Nat) [NeZero m] (s : State) : Fin m :=
  toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n)

/-- The table's slots hold the odd powers `B^(2 i + 1)` for `i < k` and `B²`. -/
def TblC (P : ChainCfg) (base : Addr) (m : Nat) [NeZero m] (B : Fin m) (k : Nat) (s : State) :
    Prop :=
  (∀ i < k, wordsVal s.mem base (P.slot i) P.M.n < m ∧
    toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base (P.slot i) P.M.n) = B ^ (2 * i + 1)) ∧
  wordsVal s.mem base (P.slot 8) P.M.n < m ∧
    toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base (P.slot 8) P.M.n) = B ^ 2

/-- A copy into the result or a table slot. -/
theorem ChainSt.copy {P : ChainCfg} {base : Addr} {size m : Nat} {s₀ s s' : State}
    (h : ChainSt P base size m s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n)))
    (hk : KeepRegs [.x1] s s') (hO : Outside base o (8 * P.M.n) s.mem s'.mem) (hL : ChainLay P size) :
    ChainSt P base size m s₀ s' := by
  have U : Unch base (chainW P) s.mem s'.mem :=
    hO.unch.cover fun w hw => op_cover ho w (by simp only [List.mem_singleton] at hw; subst hw; simp)
  refine ⟨h.scr.of_keepRegs hk (by decide), h.keep.trans (hk.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]),
    (h.unch.trans U).cover fun w hw => ?_, h.mod.unch U hL.mo_w h.scr.nowrap⟩
  rcases List.mem_append.mp hw with hw | hw <;> exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩

/-- A slot of the table is apart from the result. -/
theorem slot_acc {P : ChainCfg} {size : Nat} (hL : ChainLay P size) {i : Nat} (hi : i ≤ 8) :
    P.slot i + 8 * P.M.n ≤ P.acc ∨ P.acc + 8 * P.M.n ≤ P.slot i := by
  have := slot_le P hi; have := hL.acc_tbl; omega

theorem slot_tmp {P : ChainCfg} {size : Nat} (hL : ChainLay P size) {i : Nat} (hi : i ≤ 8) :
    P.slot i + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.slot i := by
  have := slot_le P hi; have := hL.tbl_tmp; omega

theorem slot_base {P : ChainCfg} {size : Nat} (hL : ChainLay P size) {i : Nat} (hi : i ≤ 8) :
    P.base + 8 * P.M.n ≤ P.slot i ∨ P.slot i + 8 * P.M.n ≤ P.base := by
  have := slot_le P hi; have := hL.base_tbl; omega

/-- The base survives what the chain writes. -/
theorem ChainSt.base {P : ChainCfg} {base : Addr} {size m : Nat} {s₀ s : State} (hL : ChainLay P size)
    (h : ChainSt P base size m s₀ s) :
    wordsVal s.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n := by
  have hn := h.scr.nowrap
  refine h.unch.wordsVal (fun w hw => ?_) (by have := hL.base; omega)
  simp only [chainW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact hL.acc_base.symm
  · exact hL.base_tbl
  · exact hL.base_tmp

/-- A write to the result keeps the table. -/
theorem TblC.acc {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] {B : Fin m} {k : Nat}
    (hL : ChainLay P size) {s s' : State} (hn : base.toNat + size ≤ 2 ^ 64) (h : TblC P base m B k s)
    (hk : k ≤ 8) (U : Unch base [(P.acc, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s.mem s'.mem) :
    TblC P base m B k s' := by
  have e : ∀ i ≤ 8, wordsVal s'.mem base (P.slot i) P.M.n = wordsVal s.mem base (P.slot i) P.M.n :=
    fun i hi => U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_acc hL hi
      · exact slot_tmp hL hi) (by have := slot_le P hi; have := hL.tbl; omega)
  exact ⟨fun i hi => by rw [e i (by omega)]; exact h.1 i hi, by rw [e 8 (Nat.le_refl _)]; exact h.2⟩

/-- The table: `x`, `x²` and the odd powers. -/
theorem table_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} (h : ChainSt P base size m s₀ s)
    (hB : wordsVal s₀.mem base P.base P.M.n < m) :
    WP isa (.block (ChainCfg.table P)) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' := by
  have hn := h.scr.nowrap
  have h8 := slot_mod8 P hL.tbl8
  have hle : ∀ i ≤ 8, P.slot i + 8 * P.M.n ≤ size := fun i hi => by
    have := slot_le P hi; have := hL.tbl; omega
  have hin : ∀ i ≤ 8, P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) :=
    fun i hi => slot_le P hi
  have hb := h.base hL
  rw [ChainCfg.table, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok P.M.n h.scr (hle 0 (by decide)) hL.base (h8 0) hL.base8
    ((slot_base hL (i := 0) (by decide)).symm.imp (fun h => by omega) id)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have S₁ := h.copy (Or.inr (hin 0 (by decide))) k₁ O₁ hL
  have b₁ := S₁.base hL
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok S₁.scr S₁.mod hL.mod (hle 8 (Nat.le_refl _)) hL.base hL.base (h8 8) hL.base8
    hL.base8 (by rw [b₁]; exact hB)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
  have S₂ := S₁.op hL (Or.inr (hin 8 (Nat.le_refl _))) k₂
  have v0 : ∀ {t : State}, Unch base [(P.slot 8, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s₁.mem t.mem →
      wordsVal t.mem base (P.slot 0) P.M.n = wordsVal s.mem base P.base P.M.n := fun U => by
    rw [U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P (by decide)
      · exact slot_tmp hL (by decide)) (by have := hle 0 (by decide); omega), e₁]
  have T₂ : TblC P base m (bv P base m s₀) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [v0 k₂.unch, hb]
      exact ⟨hB, by rw [Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm (e₂.trans (by rw [b₁])), Lean.Grind.Semiring.pow_two]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7)
    (fun k t => ChainSt P base size m s₀ t ∧ TblC P base m (bv P base m s₀) (k + 1) t)
    (fun k t hk ⟨St, Tt⟩ => ?_) 7 (Nat.le_refl _) s₂ ⟨S₂, T₂⟩) fun t h => h
  have Ti := Tt.1 k (by omega)
  refine WP.mono (mul_ok St.scr St.mod hL.mod (hle (k + 1) (by omega)) (hle k (by omega))
    (hle 8 (Nat.le_refl _)) (h8 _) (h8 _) (h8 _) Tt.2.1) fun u ⟨ku, ltu, eu⟩ => ?_
  refine ⟨St.op hL (Or.inr (hin (k + 1) (by omega))) ku, ?_⟩
  have e : ∀ j ≤ 8, j ≠ k + 1 →
      wordsVal u.mem base (P.slot j) P.M.n = wordsVal t.mem base (P.slot j) P.M.n := fun j hj hne =>
    ku.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P hne
      · exact slot_tmp hL hj) (by have := hle j hj; omega)
  refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt.2.1,
    by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt.2.2⟩
  rcases Nat.lt_or_ge i (k + 1) with h' | h'
  · rw [e i (by omega) (by omega)]; exact Tt.1 i h'
  · obtain rfl : i = k + 1 := by omega
    refine ⟨ltu, ?_⟩
    rw [toM_mul hm eu, Ti.2, Tt.2.2, ← Lean.Grind.Semiring.pow_add]
    congr 1

/-! ## The loop over the steps -/

/-- The table's odd powers `B^(2 i + 1)`, `i < 8`: what the loop needs of it
once slot `8` holds each step's multiplier instead of `B²`. -/
def TblO (P : ChainCfg) (base : Addr) (m : Nat) [NeZero m] (B : Fin m) (s : State) : Prop :=
  ∀ i < 8, wordsVal s.mem base (P.slot i) P.M.n < m ∧
    toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base (P.slot i) P.M.n) = B ^ (2 * i + 1)

/-- Writes to the result or to slot `8`, and to the temporary area, keep the
odd powers. -/
theorem TblO.keep {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] {B : Fin m}
    (hL : ChainLay P size) {s s' : State} (hn : base.toNat + size ≤ 2 ^ 64) (h : TblO P base m B s)
    {o : Nat} (ho : o = P.acc ∨ o = P.slot 8)
    (U : Unch base [(o, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s.mem s'.mem) : TblO P base m B s' := by
  intro i hi
  have e : wordsVal s'.mem base (P.slot i) P.M.n = wordsVal s.mem base (P.slot i) P.M.n :=
    U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases ho with rfl | rfl
        · exact slot_acc hL (by omega)
        · exact slot_apart P (by omega)
      · exact slot_tmp hL (by omega)) (by have := slot_le P (i := i) (by omega); have := hL.tbl; omega)
  rw [e]
  exact h i hi

/-- Writes to the result and the temporary area keep slot `8`. -/
theorem slot8_keep {P : ChainCfg} {base : Addr} {size : Nat} (hL : ChainLay P size) {s s' : State}
    (hn : base.toNat + size ≤ 2 ^ 64)
    (U : Unch base [(P.acc, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s.mem s'.mem) :
    wordsVal s'.mem base (P.slot 8) P.M.n = wordsVal s.mem base (P.slot 8) P.M.n :=
  U.wordsVal (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact slot_acc hL (Nat.le_refl _)
    · exact slot_tmp hL (Nat.le_refl _)) (by have := slot_le P (i := 8) (Nat.le_refl _); have := hL.tbl; omega)

/-- `x2 = k` and `x19 += x2`. -/
theorem addCount_ok (s : State) {k v : Nat} (hk : k < 2 ^ 16) (hv : v + k < 2 ^ 64)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 v) :
    WP isa (.block [.movz .x .x2 (BitVec.ofNat 16 k) 0, .add .x .x19 .x19 .x2]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (v + k) ∧ Keeps [.x2, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Size.bits, show 16 * 0 < 64 from by decide, ite_true, ite_false,
    reduceCtorEq, h19, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_zero, BitVec.shiftLeft_zero,
      BitVec.toNat_setWidth]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- A leaf of the tree: step `(k, d)`'s squarings counted in the bottom half of
`x19`, and its multiplier `B^d` copied into slot `8`. -/
theorem leaf_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    {s₀ s : State} {h k d : Nat} (hk : k < 2 ^ 16) (hd : d % 2 = 1 ∧ d ≤ 15) (_hh : h < 2 ^ 16)
    (S : ChainSt P base size m s₀ s) (h19 : s.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h)) :
    WP isa (.block (ChainCfg.leaf P (k, d))) s fun s' => ChainSt P base size m s₀ s' ∧
      s'.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h + k) ∧
      wordsVal s'.mem base (P.slot 8) P.M.n = wordsVal s.mem base (P.slot ((d - 1) / 2)) P.M.n ∧
      Unch base [(P.slot 8, 8 * P.M.n)] s.mem s'.mem := by
  rw [ChainCfg.leaf, WP.block_append_iff]
  dsimp only
  refine WP.mono (addCount_ok s hk (by omega_using [_hh, hk]) h19) fun t ⟨e19, kt⟩ => ?_
  have St : ChainSt P base size m s₀ t :=
    ⟨S.scr.of_keeps kt (by decide), S.keep.trans ((Keeps.regs kt).mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [powClob, clob]), by rw [kt.mem]; exact S.unch,
      by rw [kt.mem]; exact S.mod⟩
  have h8 := slot_le P (i := 8) (Nat.le_refl _)
  have hi8 := slot_le P (i := (d - 1) / 2) (by omega)
  refine WP.mono (copy_ok P.M.n St.scr (by have := hL.tbl; omega) (by have := hL.tbl; omega)
    (slot_mod8 P hL.tbl8 _) (slot_mod8 P hL.tbl8 _)
    ((slot_apart P (i := 8) (j := (d - 1) / 2) (by omega)).imp (fun h => by omega) id))
    fun s' ⟨e, k', O⟩ => ⟨St.copy (Or.inr h8) k' O hL, by rw [k'.gpr _ (by decide), e19], by
      rw [e, kt.mem], by rw [← kt.mem]; exact O.unch⟩

/-- Bit `b` of `x1`, into `x2`, through `x3`. -/
theorem bitTest_ok (s : State) {idx b : Nat} (hb : b < 64) (hidx : idx < 2 ^ 64)
    (hx : s.gpr .x1 = BitVec.ofNat 64 idx) :
    WP isa (.block [.lsr .x .x2 .x1 b, .movz .x .x3 1 0, .logic .and .x .x2 .x2 .x3]) s fun t =>
      isa.eval (.zero .x .x2) t = some (decide (idx / 2 ^ b % 2 = 0)) ∧ Keeps [.x2, .x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Size.bits, show 16 * 0 < 64 from by decide, hb, ite_true, ite_false,
    reduceCtorEq, hx, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · show some (_ == 0) = _
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
    simp only [read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mul_zero,
      BitVec.shiftLeft_zero]
    rw [Nat.mod_eq_of_lt hidx]
    change idx >>> b &&& 1 = 0 ↔ _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- In an aligned range of `2^(b + 1)` numbers, bit `b` tells the halves apart. -/
theorem bit_half {base idx b : Nat} (hb : base % 2 ^ (b + 1) = 0) (h1 : base ≤ idx)
    (h2 : idx < base + 2 ^ (b + 1)) : (idx / 2 ^ b % 2 = 0) ↔ idx < base + 2 ^ b := by
  have hw : 0 < 2 ^ b := Nat.two_pow_pos b
  have e2 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
  obtain ⟨q, rfl⟩ : ∃ q, base = 2 ^ (b + 1) * q :=
    ⟨base / 2 ^ (b + 1), (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hb)).symm⟩
  obtain ⟨r, rfl⟩ : ∃ r, idx = 2 ^ (b + 1) * q + r := ⟨idx - 2 ^ (b + 1) * q, by omega⟩
  have e : 2 ^ (b + 1) * q = 2 ^ b * (2 * q) := by rw [e2, Nat.mul_assoc]
  rw [e, Nat.mul_add_div hw, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  rw [e] at h2
  have hr : r < 2 ^ b * 2 := by rw [e2] at h2; omega
  rcases Nat.lt_or_ge r (2 ^ b) with h | h
  · rw [Nat.div_eq_of_lt h]; omega
  · have : r / 2 ^ b = 1 := by
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hw).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le hw).mpr (by omega)
    rw [this]; omega

/-- The tree runs the leaf of step `x1 = idx`, in `[base, base + 2^b)`. -/
theorem tree_ok {P : ChainCfg} {Q : State → Prop} {idx : Nat} (hidx : idx < ChainCfg.len P)
    (hl : ChainCfg.len P < 2 ^ 16) :
    ∀ (b base : Nat) {s : State}, b ≤ 16 → base % 2 ^ b = 0 → base ≤ idx → idx < base + 2 ^ b →
      s.gpr .x1 = BitVec.ofNat 64 idx →
      (∀ t, Keeps [.x2, .x3] s t → WP isa (.block (ChainCfg.leaf P (ChainCfg.stepAt P idx))) t Q) →
      WP isa (ChainCfg.tree P b base) s Q
  | 0, base, s, _, _, h1, h2, _, hR => by
    obtain rfl : idx = base := by simp only [Nat.pow_zero] at h2; omega
    rw [ChainCfg.tree]
    exact hR s ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | b + 1, base, s, hb16, hb, h1, h2, hx, hR => by
    have hal : base % 2 ^ b = 0 := Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ b)) (Nat.dvd_of_mod_eq_zero hb))
    have e2 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    rw [ChainCfg.tree]
    split
    · exact tree_ok hidx hl b base (by omega) hal h1 (by omega) hx hR
    · refine WP.seq (WP.mono (bitTest_ok s (b := b) (by omega) (by omega) hx) fun t ⟨ev, kt⟩ => ?_)
      have hxt : t.gpr .x1 = BitVec.ofNat 64 idx := (kt.gpr _ (by decide)).trans hx
      have hR' : ∀ u, Keeps [.x2, .x3] t u →
          WP isa (.block (ChainCfg.leaf P (ChainCfg.stepAt P idx))) u Q := fun u ku => hR u (kt.trans ku)
      have hbit := bit_half hb h1 h2
      refine WP.ite _ ev (fun hz => ?_) (fun hz => ?_)
      · exact tree_ok hidx hl b base (by omega) hal h1 (hbit.mp (of_decide_eq_true hz)) hxt hR'
      · have hge : base + 2 ^ b ≤ idx := Nat.le_of_not_lt fun h => absurd (hbit.mpr h)
          (of_decide_eq_false hz)
        refine tree_ok hidx hl b (base + 2 ^ b) (by omega) ?_ hge (by omega) hxt hR'
        rw [Nat.add_mod, hal, Nat.mod_self, Nat.zero_add, Nat.zero_mod]

/-- A loop counting the bottom half of `x19` down from `n ≥ 1`, its top half `2^32 h`. -/
theorem countLoopLo_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n h : Nat}
    (hn32 : n < 2 ^ 32)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h + (j - 1)))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .w .x19)) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have hx : (s'.read .w .x19 != 0) = decide (j - 1 ≠ 0) := by
    have e : s'.read .w .x19 = BitVec.ofNat 32 (j - 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [State.read, hz, Size.bits, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [e]
    by_cases hj : j - 1 = 0
    · rw [hj]; rfl
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hj this
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show some (s'.read .w .x19 != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show some (s'.read .w .x19 != 0) = some true
    rw [hx, decide_eq_true hj]

/-- `acc = acc^(2^k)` from `B^v`, by `k ≥ 1` squarings counted in the bottom
half of `x19`, whose top half is `2^32 h`; slot `8` is kept. -/
theorem squaresLo_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k h : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 16)
    (_hh : h < 2 ^ 16) (S : ChainSt P base size m s₀ s) (hT : TblO P base m (bv P base m s₀) s)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h + k))
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (.loop (.block (decCounter :: Impl.Mont.AArch64.mul P.M P.acc P.acc P.acc))
        (.nonzero .w .x19)) s
      fun s' => ChainSt P base size m s₀ s' ∧ TblO P base m (bv P base m s₀) s' ∧
        s'.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h) ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) ∧
        wordsVal s'.mem base (P.slot 8) P.M.n = wordsVal s.mem base (P.slot 8) P.M.n := by
  have hn := S.scr.nowrap
  refine countLoopLo_ok (n := k) (h := h) (by omega) (Inv := fun j t =>
      ChainSt P base size m s₀ t ∧ TblO P base m (bv P base m s₀) t ∧
      t.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h + j) ∧ wordsVal t.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal t.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ (k - j)) ∧
      wordsVal t.mem base (P.slot 8) P.M.n = wordsVal s.mem base (P.slot 8) P.M.n)
    (fun j t h1 h2 ⟨St, Tt, xt, lt, vt, et⟩ => ?_) (fun t ⟨St, Tt, xt, lt, vt, et⟩ => ⟨St, Tt,
      by rw [xt, Nat.add_zero], lt, by rw [vt, Nat.sub_zero], et⟩) hk1
    ⟨S, hT, h19, hlt, by rw [hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one], rfl⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok t (j := 2 ^ 32 * h + j) (by omega) (by omega) xt) fun u ⟨xu, ku⟩ => ?_
  have Su : ChainSt P base size m s₀ u :=
    ⟨St.scr.of_keeps ku (by decide), St.keep.trans ((Keeps.regs ku).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob]), by rw [ku.mem]; exact St.unch,
      by rw [ku.mem]; exact St.mod⟩
  have mu : u.mem = t.mem := ku.mem
  refine WP.mono (mul_ok Su.scr Su.mod hL.mod hL.acc hL.acc hL.acc hL.acc8 hL.acc8 hL.acc8
    (by rw [mu]; exact lt)) fun w ⟨kw, ltw, ew⟩ => ?_
  have hx : w.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * h + (j - 1)) := by
    rw [kw.gpr _ (x19_not_clob _), xu]; congr 1; omega
  have Uw := kw.unch
  rw [mu] at Uw
  refine ⟨⟨Su.op hL (Or.inl rfl) kw, Tt.keep hL hn (Or.inl rfl) Uw, hx, ltw, ?_,
    (slot8_keep hL hn Uw).trans et⟩, hx⟩
  rw [toM_mul hm (ew.trans (by rw [mu])), vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show k - (j - 1) = k - j + 1 by omega, Nat.pow_succ]
  grind

/-- The value of the chain's first steps and one more. -/
theorem chainVal_append (st : Nat × Nat) :
    ∀ (l : List (Nat × Nat)) (v : Nat), chainVal v (l ++ [st]) = chainVal v l * 2 ^ st.1 + st.2
  | [], _ => rfl
  | _ :: l, _ => chainVal_append st l _

/-- The loop's step `i` is the chain's step `L - 1 - i`. -/
theorem stepAt_eq (P : ChainCfg) {i : Nat} (hi : i < ChainCfg.len P) :
    ChainCfg.stepAt P i = P.steps[ChainCfg.len P - 1 - i]'(by unfold ChainCfg.len at hi ⊢; omega) := by
  unfold ChainCfg.stepAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_reverse]; exact hi),
    Option.getD_some, List.getElem_reverse]
  rfl

theorem stepAt_mem (P : ChainCfg) {i : Nat} (hi : i < ChainCfg.len P) : ChainCfg.stepAt P i ∈ P.steps := by
  rw [stepAt_eq P hi]; exact List.getElem_mem _

/-- `2^b` covers the steps' indices for `b = depth`. -/
theorem len_le_depth (P : ChainCfg) (h : 1 ≤ ChainCfg.len P) : ChainCfg.len P ≤ 2 ^ ChainCfg.depth P := by
  have := @Nat.lt_log2_self (ChainCfg.len P - 1)
  unfold ChainCfg.depth
  omega

theorem depth_le (P : ChainCfg) (h : ChainCfg.len P < 2 ^ 16) : ChainCfg.depth P ≤ 16 := by
  unfold ChainCfg.depth
  by_cases h0 : ChainCfg.len P - 1 = 0
  · rw [h0]; decide
  · have := (Nat.log2_lt h0 (k := 16)).mpr (by omega)
    omega

/-- What holds between steps: the chain's state, the odd powers, `i` steps to
go in the top half of `x19`, and the result `B` to the first `L - i` steps'
value. -/
def LoopInv (P : ChainCfg) (base : Addr) (size m : Nat) [NeZero m] (s₀ : State) (i : Nat)
    (s : State) : Prop :=
  ChainSt P base size m s₀ s ∧ TblO P base m (bv P base m s₀) s ∧
    s.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * i) ∧ wordsVal s.mem base P.acc P.M.n < m ∧
    toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) =
      bv P base m s₀ ^ chainVal P.first (P.steps.take (ChainCfg.len P - i))

theorem sub_top {i : Nat} (hi : i + 1 < 2 ^ 16) :
    BitVec.ofNat 64 (2 ^ 32 * (i + 1)) - BitVec.ofNat 64 (2 ^ 32) = BitVec.ofNat 64 (2 ^ 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 32 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show 2 ^ 32 * (i + 1) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * i < 2 ^ 64 by omega)]
  omega

/-- The top half of `x19` down by one, and the step's index into `x1`. -/
theorem stepCount_ok (s : State) {i : Nat} (hi : i + 1 < 2 ^ 16)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * (i + 1))) :
    WP isa (.block [.movz .x .x3 1 2, .sub .x .x19 .x19 .x3, .lsr .x .x1 .x19 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * i) ∧ t.gpr .x1 = BitVec.ofNat 64 i ∧
        Keeps [.x1, .x3, .x19] s t := by
  apply WP.of_runBlock
  have e3 : BitVec.setWidth Size.x.bits (1 : BitVec 16) <<< (16 * 2) = BitVec.ofNat 64 (2 ^ 32) := by
    decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 2 < Size.x.bits by decide,
    ite_true, e3, read_x, RegUpd.gpr_write, reduceCtorEq, ite_false, h19, BitVec.setWidth_eq,
    sub_top hi, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ 32 * i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A step of the loop: from `i + 1` steps to go to `i`. -/
theorem body_ok {P : ChainCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) (hC : ChainOk P e) {s₀ s : State} {i : Nat}
    (hi : i + 1 ≤ ChainCfg.len P) (hI : LoopInv P base size m s₀ (i + 1) s) :
    WP isa (ChainCfg.body P) s (LoopInv P base size m s₀ i) := by
  obtain ⟨S, T, h19, hlt, hv⟩ := hI
  have hn := S.scr.nowrap
  have hl : ChainCfg.len P < 2 ^ 16 := hC.len.2
  have hiL : i < ChainCfg.len P := by omega
  rw [ChainCfg.body]
  refine WP.seq (WP.mono (stepCount_ok s (by omega) h19) fun s₁ ⟨x19₁, x1₁, k₁⟩ => ?_)
  have S₁ : ChainSt P base size m s₀ s₁ :=
    ⟨S.scr.of_keeps k₁ (by decide), S.keep.trans ((Keeps.regs k₁).mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]), by rw [k₁.mem]; exact S.unch,
      by rw [k₁.mem]; exact S.mod⟩
  refine WP.seq (tree_ok hiL hl (ChainCfg.depth P) 0 (depth_le P hl) (Nat.zero_mod _) (Nat.zero_le _)
    (by rw [Nat.zero_add]; exact Nat.lt_of_lt_of_le hiL (len_le_depth P (by omega))) x1₁ fun t kt => ?_)
  have St : ChainSt P base size m s₀ t :=
    ⟨S₁.scr.of_keeps kt (by decide), S₁.keep.trans ((Keeps.regs kt).mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [powClob, clob]), by rw [kt.mem]; exact S₁.unch,
      by rw [kt.mem]; exact S₁.mod⟩
  have x19t : t.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * i) := (kt.gpr _ (by decide)).trans x19₁
  have mt : t.mem = s.mem := kt.mem.trans k₁.mem
  have hst := stepAt_eq P hiL
  have hmem := stepAt_mem P hiL
  generalize ChainCfg.stepAt P i = st at hst hmem ⊢
  obtain ⟨k, d⟩ := st
  obtain ⟨hk1, hk, hd1, hd⟩ := hC.steps _ hmem
  refine WP.mono (leaf_ok hL hk ⟨hd1, hd⟩ (by omega) St x19t) fun u ⟨Su, x19u, eu, Uu⟩ => ?_
  have Uu' : Unch base [(P.slot 8, 8 * P.M.n)] s.mem u.mem := mt ▸ Uu
  have Tu : TblO P base m (bv P base m s₀) u :=
    T.keep hL hn (Or.inr rfl) (Uu'.mono fun w hw => by simp at hw; simp [hw])
  have accu : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base P.acc P.M.n :=
    Uu'.wordsVal (fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw
      exact (slot_acc hL (Nat.le_refl _)).symm) (by have := hL.acc; omega)
  have hi8 : (d - 1) / 2 < 8 := by omega
  have Td := T ((d - 1) / 2) hi8
  rw [mt] at eu
  refine WP.seq (WP.mono (squaresLo_ok hL hm (v := chainVal P.first (P.steps.take (ChainCfg.len P - (i + 1))))
    hk1 hk (by omega) Su Tu x19u (by rw [accu]; exact hlt) (by rw [accu]; exact hv))
    fun w ⟨Sw, Tw, x19w, ltw, vw, ew⟩ => ?_)
  have e8 : wordsVal w.mem base (P.slot 8) P.M.n = wordsVal s.mem base (P.slot ((d - 1) / 2)) P.M.n :=
    ew.trans eu
  refine WP.mono (mul_ok Sw.scr Sw.mod hL.mod hL.acc hL.acc
    (by have := slot_le P (i := 8) (Nat.le_refl _); have := hL.tbl; omega) hL.acc8 hL.acc8
    (slot_mod8 P hL.tbl8 _) (by rw [e8]; exact Td.1)) fun x ⟨kx, ltx, ex⟩ => ?_
  refine ⟨Sw.op hL (Or.inl rfl) kx, Tw.keep hL hn (Or.inl rfl) kx.unch,
    by rw [kx.gpr _ (x19_not_clob _), x19w], ltx, ?_⟩
  rw [toM_mul hm ex, vw, e8, Td.2, ← Lean.Grind.Semiring.pow_add]
  congr 1
  have hlen : ChainCfg.len P - i = (ChainCfg.len P - (i + 1)) + 1 := by omega
  rw [hlen, List.take_add_one, List.getElem?_eq_getElem (by simp only [ChainCfg.len] at hiL ⊢; omega),
    Option.toList_some, chainVal_append]
  have hidx : ChainCfg.len P - (i + 1) = ChainCfg.len P - 1 - i := by omega
  simp only [hidx, ← hst]
  congr 1
  omega

/-- `x19 = 2^32 L`. -/
theorem setTop_ok (s : State) {L : Nat} (hL : L < 2 ^ 16) :
    WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 L) 2]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (2 ^ 32 * L) ∧ Keeps [.x19] s t := by
  have e : BitVec.setWidth Size.x.bits (BitVec.ofNat 16 L) <<< (16 * 2) = BitVec.ofNat 64 (2 ^ 32 * L) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hL, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show L < 2 ^ Size.x.bits by
        show L < 2 ^ 64; omega), Nat.mul_comm]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 2 < Size.x.bits by decide,
    ite_true, e, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e` of the chain;
only `powClob` and `chainW` change. -/
theorem chainPow_ok {P : ChainCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m) (hC : ChainOk P e) :
    WP isa (ChainCfg.pow P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (chainW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have S₀ : ChainSt P base size m s s := ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM⟩
  have hl : ChainCfg.len P < 2 ^ 16 := hC.len.2
  have hl1 : 1 ≤ ChainCfg.len P := hC.len.1
  rw [ChainCfg.pow]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (table_ok hL hm S₀ hB) fun s₁ ⟨S₁, T₁⟩ => ?_
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega
  have hle := slot_le P (i := (P.first - 1) / 2) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok P.M.n S₁.scr hL.acc (by have := hL.tbl; omega) hL.acc8
    (slot_mod8 P hL.tbl8 _) ((slot_acc hL (i := (P.first - 1) / 2) (by omega)).symm.imp
      (fun h => by omega) id)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂ hL
  have T₂ : TblC P base m (bv P base m s) 8 s₂ :=
    T₁.acc hL hn (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (setTop_ok s₂ hl) fun s₃ ⟨x19₃, k₃⟩ => ?_
  have S₃ : ChainSt P base size m s s₃ :=
    ⟨S₂.scr.of_keeps k₃ (by decide), S₂.keep.trans ((Keeps.regs k₃).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob]), by rw [k₃.mem]; exact S₂.unch,
      by rw [k₃.mem]; exact S₂.mod⟩
  have I₃ : LoopInv P base size m s (ChainCfg.len P) s₃ :=
    ⟨S₃, fun i hi => by rw [k₃.mem]; exact T₂.1 i hi, x19₃, by rw [k₃.mem, e₂]; exact Ti.1, by
      rw [k₃.mem, e₂, Ti.2, Nat.sub_self, List.take_zero]; congr 1
      show _ = P.first; have := hC.first; omega⟩
  refine WP.loop (M := isa) (fun j u => 1 ≤ j ∧ j ≤ ChainCfg.len P ∧ LoopInv P base size m s j u)
    (fun j u ⟨h1, h2, hu⟩ => ?_) _ s₃ ⟨hl1, Nat.le_refl _, I₃⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine WP.mono (body_ok hL hm hC h2 hu) fun u ⟨Su, Tu, x19u, ltu, vu⟩ => ?_
  have hx : (u.read .x .x19 != 0) = decide (j ≠ 0) := by
    rw [read_x, x19u]
    by_cases hj : j = 0
    · rw [hj]; rfl
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      have h0 : 2 ^ 32 * j = 0 := this
      omega
  by_cases hj : j = 0
  · subst hj
    refine Or.inl ⟨by show some (u.read .x .x19 != 0) = some false; rw [hx]; rfl,
      Su.keep, Su.unch, ltu, ?_⟩
    rw [vu, Nat.sub_zero, ChainCfg.len, List.take_length, hC.val]
  · exact Or.inr ⟨by show some (u.read .x .x19 != 0) = some true; rw [hx, decide_eq_true hj],
      j, by omega, by omega, by omega, Su, Tu, x19u, ltu, vu⟩

end VG.Proof.Weierstrass.AArch64
