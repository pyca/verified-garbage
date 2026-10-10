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
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

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

/-- The chain is the exponent's: odd digits up to 15, counts the loop can
take, and the value `e`. -/
structure ChainOk (P : ChainCfg) (e : Nat) : Prop where
  first : P.first % 2 = 1 ∧ P.first ≤ 15
  steps : ∀ st ∈ P.steps, st.1 < 2 ^ 16 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))
  val : chainVal P.first P.steps = e

/-- `ChainOk`, as a computation (`decide +kernel` evaluates it for a curve). -/
def chainCheck (first : Nat) (steps : List (Nat × Nat)) (e : Nat) : Bool :=
  first % 2 == 1 && decide (first ≤ 15) &&
    steps.all (fun st => decide (st.1 < 2 ^ 16) && (st.2 == 0 || (st.2 % 2 == 1 && decide (st.2 ≤ 15)))) &&
    chainVal first steps == e

theorem ChainOk.of_check {P : ChainCfg} {e : Nat} (h : chainCheck P.first P.steps e = true) :
    ChainOk P e := by
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨h1, h2⟩, fun st hst => ⟨(h3 st hst).1, (h3 st hst).2.imp id fun h => ⟨h.1, h.2⟩⟩, h4⟩

/-- Slot `i ≤ 8` of the table, in its area. -/
theorem slot_le (P : ChainCfg) {i : Nat} (hi : i ≤ 8) :
    P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) := by
  have := Nat.mul_le_mul_left (8 * P.M.n) hi
  simp only [ChainCfg.slot]
  omega_arith

theorem slot_apart (P : ChainCfg) {i j : Nat} (h : i ≠ j) :
    P.slot i + 8 * P.M.n ≤ P.slot j ∨ P.slot j + 8 * P.M.n ≤ P.slot i := by
  simp only [ChainCfg.slot]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * P.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith
  · right; have := Nat.mul_le_mul_left (8 * P.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith

theorem slot_mod8 (P : ChainCfg) (h : P.tbl % 8 = 0) (i : Nat) : P.slot i % 8 = 0 := by
  simp only [ChainCfg.slot]; rw [Nat.mul_assoc]; omega_arith

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
  have := slot_le P hi; have := hL.acc_tbl; omega_arith

theorem slot_tmp {P : ChainCfg} {size : Nat} (hL : ChainLay P size) {i : Nat} (hi : i ≤ 8) :
    P.slot i + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.slot i := by
  have := slot_le P hi; have := hL.tbl_tmp; omega_arith

theorem slot_base {P : ChainCfg} {size : Nat} (hL : ChainLay P size) {i : Nat} (hi : i ≤ 8) :
    P.base + 8 * P.M.n ≤ P.slot i ∨ P.slot i + 8 * P.M.n ≤ P.base := by
  have := slot_le P hi; have := hL.base_tbl; omega_arith

/-- The base survives what the chain writes. -/
theorem ChainSt.base {P : ChainCfg} {base : Addr} {size m : Nat} {s₀ s : State} (hL : ChainLay P size)
    (h : ChainSt P base size m s₀ s) :
    wordsVal s.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n := by
  have hn := h.scr.nowrap
  refine h.unch.wordsVal (fun w hw => ?_) (by have := hL.base; omega_arith)
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
      · exact slot_tmp hL hi) (by have := slot_le P hi; have := hL.tbl; omega_arith)
  exact ⟨fun i hi => by rw [e i (by omega_arith)]; exact h.1 i hi, by rw [e 8 (Nat.le_refl _)]; exact h.2⟩

/-- The table: `x`, `x²` and the odd powers. -/
theorem table_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} (h : ChainSt P base size m s₀ s)
    (hB : wordsVal s₀.mem base P.base P.M.n < m) :
    WP isa (.block (ChainCfg.table P)) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' := by
  have hn := h.scr.nowrap
  have h8 := slot_mod8 P hL.tbl8
  have hle : ∀ i ≤ 8, P.slot i + 8 * P.M.n ≤ size := fun i hi => by
    have := slot_le P hi; have := hL.tbl; omega_arith
  have hin : ∀ i ≤ 8, P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) :=
    fun i hi => slot_le P hi
  have hb := h.base hL
  rw [ChainCfg.table, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok P.M.n h.scr (hle 0 (by decide)) hL.base (h8 0) hL.base8
    ((slot_base hL (i := 0) (by decide)).symm.imp (fun h => by omega_arith) id)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
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
      · exact slot_tmp hL (by decide)) (by have := hle 0 (by decide); omega_arith), e₁]
  have T₂ : TblC P base m (bv P base m s₀) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega_arith
      rw [v0 k₂.unch, hb]
      exact ⟨hB, by rw [Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm (e₂.trans (by rw [b₁])), Lean.Grind.Semiring.pow_two]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7)
    (fun k t => ChainSt P base size m s₀ t ∧ TblC P base m (bv P base m s₀) (k + 1) t)
    (fun k t hk ⟨St, Tt⟩ => ?_) 7 (Nat.le_refl _) s₂ ⟨S₂, T₂⟩) fun t h => h
  have Ti := Tt.1 k (by omega_arith)
  refine WP.mono (mul_ok St.scr St.mod hL.mod (hle (k + 1) (by omega_arith)) (hle k (by omega_arith))
    (hle 8 (Nat.le_refl _)) (h8 _) (h8 _) (h8 _) Tt.2.1) fun u ⟨ku, ltu, eu⟩ => ?_
  refine ⟨St.op hL (Or.inr (hin (k + 1) (by omega_arith))) ku, ?_⟩
  have e : ∀ j ≤ 8, j ≠ k + 1 →
      wordsVal u.mem base (P.slot j) P.M.n = wordsVal t.mem base (P.slot j) P.M.n := fun j hj hne =>
    ku.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P hne
      · exact slot_tmp hL hj) (by have := hle j hj; omega_arith)
  refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.1,
    by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.2⟩
  rcases Nat.lt_or_ge i (k + 1) with h' | h'
  · rw [e i (by omega_arith) (by omega_arith)]; exact Tt.1 i h'
  · obtain rfl : i = k + 1 := by omega_arith
    refine ⟨ltu, ?_⟩
    rw [toM_mul hm eu, Ti.2, Tt.2.2, ← Lean.Grind.Semiring.pow_add]
    congr 1

/-- `acc = acc^(2^s)`, from `B^v`. -/
theorem squares_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k : Nat} (hs1 : 1 ≤ k) (hs : k < 2 ^ 16)
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (ChainCfg.squares P k) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
  have hn := h.scr.nowrap
  rw [ChainCfg.squares]
  refine WP.seq (WP.mono (setCounter_ok s hs) fun s₁ ⟨c₁, k₁⟩ => ?_)
  have keep₁ : KeepRegs (powClob P.M.n) s s₁ := (Keeps.regs k₁).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [powClob]
  have S₁ : ChainSt P base size m s₀ s₁ :=
    ⟨h.scr.of_keeps k₁ (by decide), h.keep.trans keep₁, by rw [k₁.mem]; exact h.unch,
      by rw [k₁.mem]; exact h.mod⟩
  refine countLoop_ok (n := k) (by omega_arith) (Inv := fun j t => ChainSt P base size m s₀ t ∧
      TblC P base m (bv P base m s₀) 8 t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      wordsVal t.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal t.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ (k - j)))
    (fun j t h1 h2 ⟨St, Tt, xt, lt, vt⟩ => ?_) (fun t ⟨St, Tt, _, lt, vt⟩ => ⟨St, Tt, lt, by
      rw [vt, Nat.sub_zero]⟩) hs1
    ⟨S₁, by unfold TblC; rw [k₁.mem]; exact hT, c₁, by rw [k₁.mem]; exact hlt,
      by rw [k₁.mem, hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one]⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok t h1 (by omega_arith) xt) fun u ⟨xu, ku⟩ => ?_
  have Su : ChainSt P base size m s₀ u :=
    ⟨St.scr.of_keeps ku (by decide), St.keep.trans ((Keeps.regs ku).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob]), by rw [ku.mem]; exact St.unch,
      by rw [ku.mem]; exact St.mod⟩
  have mu : u.mem = t.mem := ku.mem
  refine WP.mono (mul_ok Su.scr Su.mod hL.mod hL.acc hL.acc hL.acc hL.acc8 hL.acc8 hL.acc8
    (by rw [mu]; exact lt)) fun w ⟨kw, ltw, ew⟩ => ?_
  have hx : w.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [kw.gpr _ (x19_not_clob _), xu]
  have Uw := kw.unch
  rw [mu] at Uw
  refine ⟨⟨Su.op hL (Or.inl rfl) kw, Tt.acc hL hn (Nat.le_refl _) Uw,
    hx, ltw, ?_⟩, hx⟩
  rw [toM_mul hm (ew.trans (by rw [mu])), vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show k - (j - 1) = k - j + 1 by omega_arith, Nat.pow_succ]
  grind

/-- A step: `B^v` to `B^(v 2^s + d)`. -/
theorem step_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k d : Nat} (hs : k < 2 ^ 16)
    (hd : d = 0 ∨ (d % 2 = 1 ∧ d ≤ 15))
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (ChainCfg.step P (k, d)) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k + d) := by
  have hn := h.scr.nowrap
  rw [ChainCfg.step]
  have hsq : WP isa (if k = 0 then .block [] else ChainCfg.squares P k) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
    split
    · rename_i h0; subst h0
      exact WP.block_nil ⟨h, hT, hlt, by rw [hv, Nat.pow_zero, Nat.mul_one]⟩
    · exact squares_ok hL hm (by omega_arith) hs h hT hlt hv
  refine WP.seq (WP.mono hsq fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ => ?_)
  split
  · rename_i h0; subst h0
    exact WP.block_nil ⟨S₁, T₁, lt₁, by rw [v₁, Nat.add_zero]⟩
  · rename_i h0
    have hd' : d % 2 = 1 ∧ d ≤ 15 := hd.resolve_left h0
    have hi : (d - 1) / 2 < 8 := by omega_arith
    have Ti := T₁.1 _ hi
    refine WP.mono (mul_ok S₁.scr S₁.mod hL.mod hL.acc hL.acc
      (by have := slot_le P (i := (d - 1) / 2) (by omega_arith); have := hL.tbl; omega_arith) hL.acc8 hL.acc8
      (slot_mod8 P hL.tbl8 _) Ti.1) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
    refine ⟨S₁.op hL (Or.inl rfl) k₂, T₁.acc hL hn (Nat.le_refl _) k₂.unch, lt₂, ?_⟩
    rw [toM_mul hm e₂, v₁, Ti.2, ← Lean.Grind.Semiring.pow_add]
    congr 1
    omega_arith

theorem steps_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ : State} :
    ∀ (sts : List (Nat × Nat)) {s : State} {v : Nat},
      (∀ st ∈ sts, st.1 < 2 ^ 16 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))) →
      ChainSt P base size m s₀ s → TblC P base m (bv P base m s₀) 8 s →
      wordsVal s.mem base P.acc P.M.n < m →
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v →
      WP isa (ChainCfg.steps P sts) s fun s' => ChainSt P base size m s₀ s' ∧
        wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ chainVal v sts
  | [], _, _, _, h, _, hlt, hv => WP.block_nil ⟨h, hlt, hv⟩
  | (k, d) :: rest, s, v, hst, h, hT, hlt, hv => by
    rw [Impl.Weierstrass.AArch64.ChainCfg.steps]
    have h1 := hst (k, d) (List.mem_cons_self ..)
    exact WP.seq (WP.mono (step_ok hL hm h1.1 h1.2 h hT hlt hv) fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ =>
      steps_ok hL hm rest (fun st hs => hst st (List.mem_cons_of_mem _ hs)) S₁ T₁ lt₁ v₁)

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
  rw [ChainCfg.pow]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (table_ok hL hm S₀ hB) fun s₁ ⟨S₁, T₁⟩ => ?_
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega_arith
  have hle := slot_le P (i := (P.first - 1) / 2) (by omega_arith)
  refine WP.mono (copy_ok P.M.n S₁.scr hL.acc (by have := hL.tbl; omega_arith) hL.acc8
    (slot_mod8 P hL.tbl8 _) ((slot_acc hL (i := (P.first - 1) / 2) (by omega_arith)).symm.imp
      (fun h => by omega_arith) id)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂ hL
  have T₂ : TblC P base m (bv P base m s) 8 s₂ :=
    T₁.acc hL hn (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (steps_ok hL hm P.steps hC.steps S₂ T₂ (by rw [e₂]; exact Ti.1)
    (v := P.first) (by rw [e₂, Ti.2]; congr 1; have := hC.first; omega_arith)) fun s₃ ⟨S₃, lt₃, v₃⟩ =>
    ⟨S₃.keep, S₃.unch, lt₃, by rw [v₃, hC.val]⟩

end VG.Proof.Weierstrass.AArch64
