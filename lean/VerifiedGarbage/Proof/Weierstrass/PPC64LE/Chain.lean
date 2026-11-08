module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Chain
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on PPC64LE: powers by sliding windows

`VG.Impl.Weierstrass.PPC64LE.ChainCfg.pow P S` leaves `[acc]` reading (in Montgomery form) as `[base]^e`
for an exponent `e` whose chain the configuration holds (`ChainOk`), as on
AArch64 (`Proof/Weierstrass/AArch64/Chain.lean`): the table holds
`B^(2 i + 1)` and `B²` (`table_ok`), each step takes `B^v` to
`B^(v 2^s + d)` (`step_ok`: squarings by a counted loop, `squares_ok`, and a
multiplication by the table), so the steps take `B^first` to `B^e`
(`chainPow_ok`), by calls of the functions of `S`, whose own working space is
above the chain's slots (`ChainLay`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
  VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE.Mont

/-- What a power by a chain writes, for numbers of `k` words: the result, the
table and the functions' own working space. -/
def chainW (P : VG.Impl.Weierstrass.ChainCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tbl, 9 * (8 * k)), (own k, 64 * k)]

/-- The chain's slots, for numbers of `k` words: below the functions' own
working space, at multiples of 4, and apart. -/
structure ChainLay (P : VG.Impl.Weierstrass.ChainCfg) (k : Nat) : Prop where
  n : P.M.n = k
  acc : P.acc + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  tbl : P.tbl + 9 * (8 * k) ≤ own k
  acc4 : P.acc % 4 = 0
  base4 : P.base % 4 = 0
  tbl4 : P.tbl % 4 = 0
  acc_base : P.acc + 8 * k ≤ P.base ∨ P.base + 8 * k ≤ P.acc
  acc_tbl : P.acc + 8 * k ≤ P.tbl ∨ P.tbl + 9 * (8 * k) ≤ P.acc
  base_tbl : P.base + 8 * k ≤ P.tbl ∨ P.tbl + 9 * (8 * k) ≤ P.base
  fit : own k + 64 * k ≤ 8192

/-- The chain is the exponent's: odd digits up to 15, counts the loop can
take, and the value `e`. -/
structure ChainOk (P : VG.Impl.Weierstrass.ChainCfg) (e : Nat) : Prop where
  first : P.first % 2 = 1 ∧ P.first ≤ 15
  steps : ∀ st ∈ P.steps, st.1 < 2 ^ 15 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))
  val : chainVal P.first P.steps = e

/-- `ChainOk`, as a computation (`decide` evaluates it for a curve). -/
def chainCheck (first : Nat) (steps : List (Nat × Nat)) (e : Nat) : Bool :=
  first % 2 == 1 && decide (first ≤ 15) &&
    steps.all (fun st => decide (st.1 < 2 ^ 15) && (st.2 == 0 || (st.2 % 2 == 1 && decide (st.2 ≤ 15)))) &&
    chainVal first steps == e

theorem ChainOk.of_check {P : VG.Impl.Weierstrass.ChainCfg} {e : Nat} (h : chainCheck P.first P.steps e = true) :
    ChainOk P e := by
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨h1, h2⟩, fun st hst => ⟨(h3 st hst).1, (h3 st hst).2.imp id fun h => ⟨h.1, h.2⟩⟩, h4⟩

section

variable {P : VG.Impl.Weierstrass.ChainCfg} {k : Nat}

/-- Slot `i ≤ 8` of the table, in its area. -/
theorem slot_le (hL : ChainLay P k) {i : Nat} (hi : i ≤ 8) :
    P.tbl ≤ P.slot i ∧ P.slot i + 8 * k ≤ P.tbl + 9 * (8 * k) := by
  have := Nat.mul_le_mul_left (8 * k) hi
  simp only [VG.Impl.Weierstrass.ChainCfg.slot, hL.n]
  omega_arith

theorem slot_apart (hL : ChainLay P k) {i j : Nat} (h : i ≠ j) :
    P.slot i + 8 * k ≤ P.slot j ∨ P.slot j + 8 * k ≤ P.slot i := by
  simp only [VG.Impl.Weierstrass.ChainCfg.slot, hL.n]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * k) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith
  · right; have := Nat.mul_le_mul_left (8 * k) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith

theorem slot_mod4 (hL : ChainLay P k) (i : Nat) : P.slot i % 4 = 0 := by
  have := hL.tbl4
  simp only [VG.Impl.Weierstrass.ChainCfg.slot]
  rw [Nat.mul_assoc]; omega_arith

theorem slot_own (hL : ChainLay P k) {i : Nat} (hi : i ≤ 8) : P.slot i + 8 * k ≤ own k := by
  have := slot_le hL hi; have := hL.tbl; omega_arith

theorem slot_acc (hL : ChainLay P k) {i : Nat} (hi : i ≤ 8) :
    P.slot i + 8 * k ≤ P.acc ∨ P.acc + 8 * k ≤ P.slot i := by
  have := slot_le hL hi; have := hL.acc_tbl; omega_arith

theorem slot_base (hL : ChainLay P k) {i : Nat} (hi : i ≤ 8) :
    P.base + 8 * k ≤ P.slot i ∨ P.slot i + 8 * k ≤ P.base := by
  have := slot_le hL hi; have := hL.base_tbl; omega_arith

/-- What holds throughout the power, from `s₀`. -/
structure ChainSt (P : VG.Impl.Weierstrass.ChainCfg) (k : Nat) (base : Addr) (s₀ s : State) : Prop where
  ws : WsReg s base
  keep : Rk powClob s₀ s
  unch : Unch base (chainW P k) s₀.mem s.mem

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.CallKeep.unch {n : Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep n base o s s') : Unch base [(o, 8 * n), (own n, 64 * n)] s.mem s'.mem := h.mem

/-- A call writing the result or a table slot. -/
theorem ChainSt.call {base : Addr} {s₀ s s' : State} (h : ChainSt P k base s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * k ≤ P.tbl + 9 * (8 * k))) (hk : CallKeep k base o s s') :
    ChainSt P k base s₀ s' := by
  refine ⟨h.ws.of_rk (hk.rk (rs := powClob)), h.keep.trans (hk.rk (rs := powClob)),
    (h.unch.trans hk.mem).cover fun w hw => ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
  · rcases ho with rfl | ho
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ho.1, ho.2⟩
  · exact ⟨_, by simp [chainW], Nat.le_refl _, Nat.le_refl _⟩

/-- A copy into the result or a table slot. -/
theorem ChainSt.copy {base : Addr} {s₀ s s' : State} (h : ChainSt P k base s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * k ≤ P.tbl + 9 * (8 * k)))
    (hk : Kp [.r4] s s') (hO : Outside base o (8 * k) s.mem s'.mem) :
    ChainSt P k base s₀ s' := by
  refine ⟨h.ws.of_kp hk, h.keep.trans (hk.rk (rs' := powClob)), (h.unch.trans hO.unch).cover fun w hw => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
  · rcases ho with rfl | ho
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ho.1, ho.2⟩

/-- `B`, what the base reads as. -/
abbrev bv (P : VG.Impl.Weierstrass.ChainCfg) (k : Nat) (base : Addr) (m : Nat) [NeZero m] (s : State) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem base P.base k)

/-- The base survives what the chain writes. -/
theorem ChainSt.base {base : Addr} {s₀ s : State} (hL : ChainLay P k) (h : ChainSt P k base s₀ s) :
    wordsVal s.mem base P.base k = wordsVal s₀.mem base P.base k := by
  have hn := h.ws.nowrap
  refine h.unch.wordsVal (fun w hw => ?_) (by have := hL.base; have := hL.fit; omega_arith)
  simp only [chainW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact hL.acc_base.symm
  · exact hL.base_tbl
  · exact .inl hL.base

/-- The table's slots hold the odd powers `B^(2 i + 1)` for `i < j` and `B²`. -/
def TblC (P : VG.Impl.Weierstrass.ChainCfg) (k : Nat) (base : Addr) (m : Nat) [NeZero m] (B : Fin m) (j : Nat)
    (s : State) : Prop :=
  (∀ i < j, wordsVal s.mem base (P.slot i) k < m ∧
    toM m (2 ^ (64 * k)) (wordsVal s.mem base (P.slot i) k) = B ^ (2 * i + 1)) ∧
  wordsVal s.mem base (P.slot 8) k < m ∧
    toM m (2 ^ (64 * k)) (wordsVal s.mem base (P.slot 8) k) = B ^ 2

/-- A write of the result keeps the table. -/
theorem TblC.acc {base : Addr} {m : Nat} [NeZero m] {B : Fin m} {j : Nat} (hL : ChainLay P k)
    {s s' : State} (h : TblC P k base m B j s) (hj : j ≤ 8)
    (U : Unch base [(P.acc, 8 * k), (own k, 64 * k)] s.mem s'.mem) : TblC P k base m B j s' := by
  have e : ∀ i ≤ 8, wordsVal s'.mem base (P.slot i) k = wordsVal s.mem base (P.slot i) k :=
    fun i hi => U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_acc hL hi
      · exact .inl (slot_own hL hi)) (by have := slot_own hL hi; have := hL.fit; omega_arith)
  exact ⟨fun i hi => by rw [e i (by omega_arith)]; exact h.1 i hi, by rw [e 8 (Nat.le_refl _)]; exact h.2⟩

end

variable {P : VG.Impl.Weierstrass.ChainCfg} {S : Impl.Weierstrass.Mont.Modulus} {k m : Nat} [NeZero m]

/-- The odd powers after `x` and `x²`: slots `1` to `j`. -/
theorem odds_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {s₀ : State} :
    ∀ (j : Nat), j ≤ 7 → ∀ {s : State}, ChainSt P k base s₀ s → TblC P k base m (bv P k base m s₀) 1 s →
      WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.odds P S j) s fun s' =>
        ChainSt P k base s₀ s' ∧ TblC P k base m (bv P k base m s₀) (j + 1) s'
  | 0, _, _, St, Tt => WP.block_nil ⟨St, Tt⟩
  | j + 1, hj, s, St, Tt => by
    rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.odds]
    refine WP.seq (WP.mono (odds_ok hkS hmS hM hL hm j (by omega) St Tt) fun t ⟨St', Tt'⟩ => ?_)
    have hn := St'.ws.nowrap
    have Ti := Tt'.1 j (by omega)
    obtain ⟨cv, w, m', k', d⟩ := S
    dsimp only at hkS hmS
    subst hkS hmS
    refine WP.mono (mulCall_ok hM St'.ws (slot_own hL (i := j + 1) (by omega)) (slot_own hL (i := j) (by omega))
      (slot_own hL (i := 8) (Nat.le_refl _)) Tt'.2.1) fun u ⟨ku, ltu, eu⟩ => ?_
    refine ⟨St'.call (Or.inr (slot_le hL (i := j + 1) (by omega))) ku, ?_⟩
    have e : ∀ i ≤ 8, i ≠ j + 1 → wordsVal u.mem base (P.slot i) k' = wordsVal t.mem base (P.slot i) k' :=
      fun i hi hne => ku.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact slot_apart hL hne
        · exact .inl (slot_own hL hi)) (by have := slot_own hL hi; have := hL.fit; omega_arith)
    refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt'.2.1,
      by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt'.2.2⟩
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [e i (by omega) (by omega)]; exact Tt'.1 i h'
    · obtain rfl : i = j + 1 := by omega
      refine ⟨ltu, ?_⟩
      rw [toM_mul hm eu, Ti.2, Tt'.2.2, ← Lean.Grind.Semiring.pow_add]
      congr 1

/-- The table: `x`, `x²` and the odd powers. -/
theorem table_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {s : State} (hw : WsReg s base)
    (hB : wordsVal s.mem base P.base k < m) :
    WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.table P S) s fun s' =>
      ChainSt P k base s s' ∧ TblC P k base m (bv P k base m s) 8 s' := by
  have hn := hw.nowrap
  have ho := own_lt k
  have S₀ : ChainSt P k base s s := ⟨hw, Rk.refl _ _, Unch.refl _ _ _⟩
  rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.table, hL.n]
  refine WP.seq (WP.mono (copy_ok k hw.ws hw.at3 (o := P.slot 0) (a := P.base) (slot_mod4 hL 0) hL.base4
    (by have := slot_own hL (i := 0) (by decide); have := hL.fit; omega_arith)
    (by have := hL.base; have := hL.fit; omega_arith)
    ((slot_base hL (i := 0) (by decide)).symm.imp (fun h => by omega_arith) id)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have S₁ := S₀.copy (Or.inr (slot_le hL (i := 0) (by decide))) k₁ O₁
  have b₁ := S₁.base hL
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  refine WP.seq (WP.mono (mulCall_ok hM S₁.ws (slot_own hL (i := 8) (Nat.le_refl _)) hL.base hL.base
    (by rw [b₁]; exact hB)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have S₂ := S₁.call (Or.inr (slot_le hL (i := 8) (Nat.le_refl _))) k₂
  have v0 : wordsVal s₂.mem base (P.slot 0) k' = wordsVal s.mem base P.base k' := by
    rw [k₂.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart hL (by decide)
      · exact .inl (slot_own hL (i := 0) (by decide))) (by have := slot_own hL (i := 0) (by decide); omega_arith), e₁]
  have T₂ : TblC P k' base m' (bv P k' base m' s) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [v0]
      exact ⟨hB, by rw [Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm (e₂.trans (by rw [b₁])), Lean.Grind.Semiring.pow_two]
  exact odds_ok (S := ⟨cv, w, m', k', d⟩) rfl rfl hM hL hm 7 (Nat.le_refl _) S₂ T₂

/-- `acc = acc^(2^j)`, from `B^v`. -/
theorem squares_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {s₀ s : State} {v j : Nat} (hj1 : 1 ≤ j) (hj : j < 2 ^ 15)
    (h : ChainSt P k base s₀ s) (hT : TblC P k base m (bv P k base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc k < m)
    (hv : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) = bv P k base m s₀ ^ v) :
    WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.squares P S j) s fun s' => ChainSt P k base s₀ s' ∧
      TblC P k base m (bv P k base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) = bv P k base m s₀ ^ (v * 2 ^ j) := by
  have hn := h.ws.nowrap
  rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.squares]
  refine WP.seq (wp_step (exec_li hj) (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 j) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 j := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have S₁ : ChainSt P k base s₀ s₁ :=
    ⟨h.ws.of_kp K₁, h.keep.trans (K₁.rk (rs' := powClob)), by rw [m₁]; exact h.unch⟩
  refine countLoop_ok (n := j) (Inv := fun i t => ChainSt P k base s₀ t ∧
      TblC P k base m (bv P k base m s₀) 8 t ∧ t.gpr .r31 = BitVec.ofNat 64 i ∧
      wordsVal t.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal t.mem base P.acc k) = bv P k base m s₀ ^ (v * 2 ^ (j - i)))
    (fun i t hi => hi.2.2.1) (fun i t h1 h2 ⟨St, Tt, xt, lt, vt⟩ => ?_) (fun t ⟨St, Tt, _, lt, vt⟩ => ⟨St, Tt, lt, by
      rw [vt, Nat.sub_zero]⟩) hj1 (by omega)
    ⟨S₁, by unfold TblC; rw [m₁]; exact hT, c₁, by rw [m₁]; exact hlt,
      by rw [m₁, hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one]⟩
  refine WP.seq (wp_decCounter h1 xt (WP.block_nil ?_))
  generalize hu : t.write .r31 (BitVec.ofNat 64 (i - 1)) = u
  have Ku : Kp [.r31] t u := by rw [← hu]; exact Kp.write _ _ (by decide)
  have mu : u.mem = t.mem := by rw [← hu]; rfl
  have xu : u.gpr .r31 = BitVec.ofNat 64 (i - 1) := by rw [← hu]; simp only [write_gpr, ite_true]
  have Su : ChainSt P k base s₀ u :=
    ⟨St.ws.of_kp Ku, St.keep.trans (Ku.rk (rs' := powClob)), by rw [mu]; exact St.unch⟩
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  refine WP.mono (mulCall_ok hM Su.ws hL.acc hL.acc hL.acc (by rw [mu]; exact lt)) fun w' ⟨kw, ltw, ew⟩ => ?_
  have hx : w'.gpr .r31 = BitVec.ofNat 64 (i - 1) := by rw [kw.gpr _ (by decide), xu]
  have Uw : Unch base [(P.acc, 8 * k'), (own k', 64 * k')] t.mem w'.mem := by rw [← mu]; exact kw.mem
  refine ⟨Su.call (Or.inl rfl) kw, Tt.acc hL (Nat.le_refl _) Uw, hx, ltw, ?_⟩
  rw [toM_mul hm (ew.trans (by rw [mu])), vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show j - (i - 1) = j - i + 1 by omega, Nat.pow_succ]
  grind

/-- A step: `B^v` to `B^(v 2^j + d)`. -/
theorem step_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {s₀ s : State} {v j d : Nat} (hj : j < 2 ^ 15)
    (hd : d = 0 ∨ (d % 2 = 1 ∧ d ≤ 15))
    (h : ChainSt P k base s₀ s) (hT : TblC P k base m (bv P k base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc k < m)
    (hv : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) = bv P k base m s₀ ^ v) :
    WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.step P S (j, d)) s fun s' => ChainSt P k base s₀ s' ∧
      TblC P k base m (bv P k base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) = bv P k base m s₀ ^ (v * 2 ^ j + d) := by
  have hn := h.ws.nowrap
  rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.step]
  have hsq : WP isa (if j = 0 then .block [] else VG.Impl.Weierstrass.PPC64LE.ChainCfg.squares P S j) s fun s' =>
      ChainSt P k base s₀ s' ∧ TblC P k base m (bv P k base m s₀) 8 s' ∧
      wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) = bv P k base m s₀ ^ (v * 2 ^ j) := by
    split
    · rename_i h0; subst h0
      exact WP.block_nil ⟨h, hT, hlt, by rw [hv, Nat.pow_zero, Nat.mul_one]⟩
    · exact squares_ok hkS hmS hM hL hm (by omega) hj h hT hlt hv
  refine WP.seq (WP.mono hsq fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ => ?_)
  split
  · rename_i h0; subst h0
    exact WP.block_nil ⟨S₁, T₁, lt₁, by rw [v₁, Nat.add_zero]⟩
  · rename_i h0
    have hd' : d % 2 = 1 ∧ d ≤ 15 := hd.resolve_left h0
    have hi : (d - 1) / 2 < 8 := by omega
    have Ti := T₁.1 _ hi
    obtain ⟨cv, w, m', k', d'⟩ := S
    dsimp only at hkS hmS
    subst hkS hmS
    refine WP.mono (mulCall_ok hM S₁.ws hL.acc hL.acc (slot_own hL (i := (d - 1) / 2) (by omega)) Ti.1)
      fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
    refine ⟨S₁.call (Or.inl rfl) k₂, T₁.acc hL (Nat.le_refl _) k₂.unch, lt₂, ?_⟩
    rw [toM_mul hm e₂, v₁, Ti.2, ← Lean.Grind.Semiring.pow_add]
    congr 1
    omega

theorem steps_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {s₀ : State} :
    ∀ (sts : List (Nat × Nat)) {s : State} {v : Nat},
      (∀ st ∈ sts, st.1 < 2 ^ 15 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))) →
      ChainSt P k base s₀ s → TblC P k base m (bv P k base m s₀) 8 s →
      wordsVal s.mem base P.acc k < m →
      toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) = bv P k base m s₀ ^ v →
      WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.steps P S sts) s fun s' => ChainSt P k base s₀ s' ∧
        wordsVal s'.mem base P.acc k < m ∧
        toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) = bv P k base m s₀ ^ chainVal v sts
  | [], _, _, _, h, _, hlt, hv => WP.block_nil ⟨h, hlt, hv⟩
  | (j, d) :: rest, s, v, hst, h, hT, hlt, hv => by
    rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.steps]
    have h1 := hst (j, d) (List.mem_cons_self ..)
    exact WP.seq (WP.mono (step_ok hkS hmS hM hL hm h1.1 h1.2 h hT hlt hv) fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ =>
      steps_ok hkS hmS hM hL hm rest (fun st hs => hst st (List.mem_cons_of_mem _ hs)) S₁ T₁ lt₁ v₁)

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e` of the chain,
modulo `m` on numbers of `k` words (the functions' `S.m` and `S.k`); only
`powClob` and `chainW` change, as for `pow_ok`. -/
theorem chainPow_ok (hkS : S.k = k) (hmS : S.m = m) (hM : ModOk k m) (hL : ChainLay P k)
    (hm : UnitMod m (2 ^ (64 * k))) {base : Addr} {e : Nat} {s : State} (hs : WsReg s base)
    (hB : wordsVal s.mem base P.base k < m) (hC : ChainOk P e) :
    WP isa (VG.Impl.Weierstrass.PPC64LE.ChainCfg.pow P S) s fun s' => Rk powClob s s' ∧ Unch base (chainW P k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) =
        toM m (2 ^ (64 * k)) (wordsVal s.mem base P.base k) ^ e := by
  have hn := hs.nowrap
  have ho := own_lt k
  rw [VG.Impl.Weierstrass.PPC64LE.ChainCfg.pow, hL.n]
  refine WP.seq (WP.mono (table_ok hkS hmS hM hL hm hs hB) fun s₁ ⟨S₁, T₁⟩ => ?_)
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega
  have hle := slot_own hL (i := (P.first - 1) / 2) (by omega)
  refine WP.seq (WP.mono (copy_ok k S₁.ws.ws S₁.ws.at3 (o := P.acc) (a := P.slot ((P.first - 1) / 2)) hL.acc4
    (slot_mod4 hL _) (by have := hL.acc; have := hL.fit; omega_arith) (by have := hL.fit; omega_arith)
    ((slot_acc hL (i := (P.first - 1) / 2) (by omega)).symm.imp (fun h => by omega_arith) id))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂
  have T₂ : TblC P k base m (bv P k base m s) 8 s₂ :=
    T₁.acc hL (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (steps_ok hkS hmS hM hL hm P.steps hC.steps S₂ T₂ (by rw [e₂]; exact Ti.1)
    (v := P.first) (by rw [e₂, Ti.2]; congr 1; have := hC.first; omega)) fun s₃ ⟨S₃, lt₃, v₃⟩ =>
    ⟨S₃.keep, S₃.unch, lt₃, by rw [v₃, hC.val]⟩

end VG.Proof.Weierstrass.PPC64LE
