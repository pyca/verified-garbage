module

import VerifiedGarbage.Proof.Weierstrass.X86.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Impl.Weierstrass.X86.PowWindow
import VerifiedGarbage.Proof.Mont.X86.Instr

-- separate module: for any modulus and slots, so for every power by a public exponent on x86, not only the decompression's root that uses it first
/-!
# Powers by a public exponent, with a table of saved powers

`tabRun ops (a, T)` is what a sequence of `TabOp`s makes of the exponents of
the accumulator (`a`) and of the saved powers (`T`, zero for a slot not yet
written), or `none` if it reads a slot before writing it. The code of a
sequence that runs (`tabPower_ok`) leaves the accumulator reading as the base
to the exponent it ends with, and `windowOps e bits` ends with `e`
(`windowOps_run`), whatever `e` is: `windowPower_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-! ## The exponents a sequence reaches -/

def tabStep : TabOp → Nat × List Nat → Option (Nat × List Nat)
  | .get i, (_, T) => if T.getD i 0 = 0 then none else some (T.getD i 0, T)
  | .put i, (a, T) => if i < T.length then some (a, T.set i a) else none
  | .squares n, (a, T) => if n < 2 ^ 32 then some (a * 2 ^ n, T) else none
  | .mul i, (a, T) => if T.getD i 0 = 0 then none else some (a + T.getD i 0, T)

def tabRun : List TabOp → Nat × List Nat → Option (Nat × List Nat)
  | [], v => some v
  | op :: ops, v => (tabStep op v).bind (tabRun ops)

theorem tabRun_append (a b : List TabOp) (v : Nat × List Nat) :
    tabRun (a ++ b) v = (tabRun a v).bind (tabRun b) := by
  induction a generalizing v with
  | nil => rfl
  | cons op a ih =>
    simp only [List.cons_append, tabRun]
    cases tabStep op v with
    | none => rfl
    | some v' => exact ih v'

theorem tabRun_squaresThen {k : Nat} (hk : k < 2 ^ 32) (ops : List TabOp) (a : Nat) (T : List Nat) :
    tabRun (squaresThen k ops) (a, T) = tabRun ops (a * 2 ^ k, T) := by
  unfold squaresThen
  split
  next h => rw [h, Nat.pow_zero, Nat.mul_one]
  next h => simp only [tabRun, tabStep, hk, ↓reduceIte, Option.bind_some]

/-- The windows of `e`, with the odd powers below 16 saved. -/
theorem windowFrom_run {T : List Nat} (hT : ∀ i < 8, T.getD i 0 = 2 * i + 1) :
    ∀ (f e k : Nat) (ops : List TabOp) (a : Nat), 0 < e → e < 2 ^ f → k + f < 2 ^ 32 →
      4 + f < 2 ^ 32 → tabRun (windowFrom f e k ops) (a, T) = tabRun ops (e * 2 ^ k, T)
  | 0, e, k, ops, a, h0, he, _, _ => by omega_using [h0, he]
  | f + 1, e, k, ops, a, h0, he, hk, hf => by
    have he' : e < 2 * 2 ^ f := by rw [Nat.pow_succ] at he; omega_using [he]
    unfold windowFrom
    split
    next h2 =>
      rw [windowFrom_run hT f (e / 2) (k + 1) ops a (by omega_using [h0, h2])
        (by omega_using [he']) (by omega_using [hk]) (by omega_using [hf]), Nat.pow_succ,
        ← Nat.mul_assoc, Nat.mul_right_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)]
    next h2 =>
      split
      next h16 =>
        have hg : T.getD (e / 2) 0 = e := by
          rw [hT _ (by omega_using [h16])]; omega_using [h2]
        simp only [tabRun, tabStep, hg, Nat.ne_of_gt h0, ↓reduceIte, Option.bind_some]
        exact tabRun_squaresThen (by omega_using [hk]) ops e T
      next h16 =>
        have hg : T.getD (e % 16 / 2) 0 = e % 16 := by
          rw [hT _ (by omega_using [])]; omega_using [h2]
        have hpos : e % 16 ≠ 0 := by omega_using [h2]
        rw [windowFrom_run hT f (e / 16) 4 _ a (by omega_using [h16]) (by omega_using [he'])
          (by omega_using [hf]) (by omega_using [hf])]
        simp only [tabRun, tabStep, hg, hpos, ↓reduceIte, Option.bind_some]
        rw [show e / 16 * 2 ^ 4 + e % 16 = e by omega_using []]
        exact tabRun_squaresThen (by omega_using [hk]) ops e T

theorem windowTable_run : tabRun windowTable (1, List.replicate 9 0) =
    some (15, [1, 3, 5, 7, 9, 11, 13, 15, 2]) := by decide

/-- `windowOps e bits` reaches `e`. -/
theorem windowOps_run {e bits : Nat} (h0 : 0 < e) (he : e < 2 ^ bits) (hb : bits + 4 < 2 ^ 32) :
    tabRun (windowOps e bits) (1, List.replicate 9 0) =
      some (e, [1, 3, 5, 7, 9, 11, 13, 15, 2]) := by
  rw [windowOps, tabRun_append, windowTable_run, Option.bind_some,
    windowFrom_run (by decide) bits e 0 [] 15 h0 he (by omega_using [hb]) (by omega_using [hb]),
    Nat.pow_zero, Nat.mul_one]
  rfl

/-! ## The code of a sequence -/

/-- Where the saved powers are: slots below the functions' working space,
apart from each other, from what a power writes, from its base and from the
modulus. -/
structure TabLay (P : PowCfg) (wk : Nat) (tab : List Nat) : Prop where
  le : ∀ o ∈ tab, o + 8 * P.M.n ≤ wk
  apart : ∀ o ∈ tab, ∀ w ∈ powWx P wk, o + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ o
  base : ∀ o ∈ tab, P.base + 8 * P.M.n ≤ o ∨ o + 8 * P.M.n ≤ P.base
  mo : ∀ o ∈ tab, P.M.mo + 8 * P.M.n ≤ o ∨ o + 8 * P.M.n ≤ P.M.mo
  pair : tab.Pairwise fun a b => a + 8 * P.M.n ≤ b ∨ b + 8 * P.M.n ≤ a

/-- What a sequence writes besides a power's own slots. -/
def tabW (P : PowCfg) (tab : List Nat) : List (Nat × Nat) := tab.map fun o => (o, 8 * P.M.n)

theorem getD_mem_tab {tab : List Nat} {i : Nat} (hi : i < tab.length) : tab.getD i 0 ∈ tab := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem TabLay.ne {P : PowCfg} {wk : Nat} {tab : List Nat} (h : TabLay P wk tab) {i j : Nat}
    (hi : i < tab.length) (hj : j < tab.length) (hij : i ≠ j) :
    tab.getD j 0 + 8 * P.M.n ≤ tab.getD i 0 ∨ tab.getD i 0 + 8 * P.M.n ≤ tab.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some]
  have hp := List.pairwise_iff_getElem.mp h.pair
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact (hp i j hi hj hlt).symm
  · exact hp j i hj hi hlt

/-- The saved powers: slot `i` reads as the base to `T[i]`, unless that is
zero. -/
structure TabOk (P : PowCfg) (base : Addr) (m : Nat) [NeZero m] (B : Fin m) (tab T : List Nat)
    (mem : Mem) : Prop where
  len : T.length = tab.length
  ok : ∀ i, i < tab.length → T.getD i 0 ≠ 0 →
    wordsVal mem base (tab.getD i 0) P.M.n < m ∧
    toM m (2 ^ (64 * P.M.n)) (wordsVal mem base (tab.getD i 0) P.M.n) = B ^ T.getD i 0

theorem TabOk.unch {P : PowCfg} {base : Addr} {m : Nat} [NeZero m] {B : Fin m} {tab T : List Nat}
    {mem mem' : Mem} (h : TabOk P base m B tab T mem) {W : List (Nat × Nat)}
    (U : Unch base W mem mem')
    (hW : ∀ o ∈ tab, ∀ w ∈ W, o + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ o)
    (hle : ∀ o ∈ tab, o + 8 * P.M.n ≤ 2 ^ 64) : TabOk P base m B tab T mem' := by
  refine ⟨h.len, fun i hi h0 => ?_⟩
  rw [U.wordsVal (hW _ (getD_mem_tab hi)) (hle _ (getD_mem_tab hi))]
  exact h.ok i hi h0

theorem getD_pos_lt {T : List Nat} {i : Nat} (h : T.getD i 0 ≠ 0) : i < T.length := by
  by_contra hn
  exact h (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]; rfl)

theorem tabOp_ok {P : PowCfg} {F : Impl.Weierstrass.Mont.Modulus} {base : Addr} {size wk m t : Nat}
    [NeZero m] {B : Fin m} {tab : List Nat} {s : State} {v v' : Nat × List Nat}
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hT : TabLay P wk tab) (op : TabOp) (hr : tabStep op v = some v')
    (I : PowerState P base size m B v.1 t s) (TO : TabOk P base m B tab v.2 s.mem) :
    WP isa (tabOp P F tab op) s fun u =>
      PowerState P base size m B v'.1 t u ∧ TabOk P base m B tab v'.2 u.mem ∧
      Keeps powClob s u ∧ Unch base (powWx P wk ++ tabW P tab) s.mem u.mem := by
  obtain ⟨a, T⟩ := v
  have hn := I.scr.nowrap
  have hsz := hW.size
  have hown := hW.toCallCfg.own_le
  have hacc := hL.acc
  have hle : ∀ o ∈ tab, o + 8 * P.M.n ≤ 2 ^ 64 := fun o ho => by
    have := hT.le o ho; omega_using [this, hown]
  have hta : ∀ o ∈ tab, o + 8 * P.M.n ≤ P.acc ∨ P.acc + 8 * P.M.n ≤ o := fun o ho =>
    hT.apart o ho (P.acc, 8 * P.M.n) (by simp [powWx, powW])
  have htt : ∀ o ∈ tab, o + 8 * P.M.n ≤ P.tmp ∨ P.tmp + 8 * P.M.n ≤ o := fun o ho =>
    hT.apart o ho (P.tmp, 8 * P.M.n) (by simp [powWx, powW])
  cases op with
  | get i =>
    simp only [tabStep] at hr
    split at hr
    · exact absurd hr (by simp)
    next h0 =>
      cases Option.some.inj hr
      have hi : i < tab.length := TO.len ▸ getD_pos_lt h0
      have hmem := getD_mem_tab hi
      have hto := hT.le _ hmem
      have hap := hta _ hmem
      obtain ⟨lt, val⟩ := TO.ok i hi h0
      refine WP.mono (copy_ok (2 * P.M.n) I.scr (o := P.acc) (a := tab.getD i 0)
        (by omega_using [hacc]) (by omega_using [hto, hown, hsz]) (by omega_using [hap]))
        fun u ⟨V, K, O⟩ => ?_
      rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega_using []] at O
      have U : Unch base (powWx P wk) s.mem u.mem := O.unch.mono fun w hw => by
        simp only [List.mem_singleton] at hw
        simp [hw, powWx, powW]
      have ea : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base (tab.getD i 0) P.M.n := by
        rw [wordsVal_eq_val32, V, ← wordsVal_eq_val32]
      have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.tmp P.M.n :=
        O.wordsVal hL.acc_tmp.symm (by have := hL.tmp; omega_using [hn, this])
      refine ⟨I.rebuild hL hW (I.scr.of_keeps K (by decide)) U (ea ▸ lt) ?_ (et ▸ I.tmp_lt) ?_,
        TO.unch U hT.apart hle, K.mono (by decide), U.mono fun w hw => List.mem_append_left _ hw⟩
      · rw [ea]; exact val
      · rw [et]; exact I.tmp_val
  | put i =>
    simp only [tabStep] at hr
    split at hr
    next hi' =>
      cases Option.some.inj hr
      have hi : i < tab.length := TO.len ▸ hi'
      have hmem := getD_mem_tab hi
      have hto := hT.le _ hmem
      have hap := hta _ hmem
      refine WP.mono (copy_ok (2 * P.M.n) I.scr (o := tab.getD i 0) (a := P.acc)
        (by omega_using [hto, hown, hsz]) (by omega_using [hacc]) (by omega_using [hap]))
        fun u ⟨V, K, O⟩ => ?_
      rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega_using []] at O
      have eo : wordsVal u.mem base (tab.getD i 0) P.M.n = wordsVal s.mem base P.acc P.M.n := by
        rw [wordsVal_eq_val32, V, ← wordsVal_eq_val32]
      have ea : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base P.acc P.M.n :=
        O.wordsVal hap.symm (by omega_using [hn, hacc])
      have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.tmp P.M.n :=
        O.wordsVal (htt _ hmem).symm (by have := hL.tmp; omega_using [hn, this])
      have eb : wordsVal u.mem base P.base P.M.n = wordsVal s.mem base P.base P.M.n :=
        O.wordsVal (hT.base _ hmem) (by have := hL.base; omega_using [hn, this])
      refine ⟨⟨I.scr.of_keeps K (by decide), I.mod.unch O.unch (fun w hw => by
          rw [List.mem_singleton.mp hw]; exact hT.mo _ hmem) (by omega_using [hn]),
          eb ▸ I.base_lt, by rw [eb]; exact I.base_val, ea ▸ I.acc_lt, by rw [ea]; exact I.acc_val,
          et ▸ I.tmp_lt, by rw [et]; exact I.tmp_val⟩,
        ⟨by rw [List.length_set]; exact TO.len, fun j hj h0 => ?_⟩, K.mono (by decide),
        O.unch.mono fun w hw => List.mem_append_right _ (by
          rw [List.mem_singleton.mp hw]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩)⟩
      by_cases hji : i = j
      · subst hji
        have hg : (T.set i a).getD i 0 = a := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi']; rfl
        rw [hg, eo]
        exact ⟨I.acc_lt, I.acc_val⟩
      · have hg : (T.set i a).getD j 0 = T.getD j 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hji, ← List.getD_eq_getElem?_getD]
        rw [hg] at h0 ⊢
        rw [O.wordsVal (hT.ne hi hj hji) (hle _ (getD_mem_tab hj))]
        exact TO.ok j hj h0
    · exact absurd hr (by simp)
  | squares n =>
    simp only [tabStep] at hr
    split at hr
    next hn32 =>
      cases Option.some.inj hr
      exact WP.mono (squareRun_ok I hL hW hm n hn32) fun u ⟨Iu, K, U⟩ =>
        ⟨Iu, TO.unch U hT.apart hle, K, U.mono fun w hw => List.mem_append_left _ hw⟩
    · exact absurd hr (by simp)
  | mul i =>
    simp only [tabStep] at hr
    split at hr
    · exact absurd hr (by simp)
    next h0 =>
      cases Option.some.inj hr
      have hi : i < tab.length := TO.len ▸ getD_pos_lt h0
      obtain ⟨lt, val⟩ := TO.ok i hi h0
      exact WP.mono (powerMul_ok I hL hW hm (hT.le _ (getD_mem_tab hi)) lt val) fun u ⟨Iu, K, U⟩ =>
        ⟨Iu, TO.unch U hT.apart hle, K.mono (by decide), U.mono fun w hw => List.mem_append_left _ hw⟩

theorem tabChain_ok {P : PowCfg} {F : Impl.Weierstrass.Mont.Modulus} {base : Addr} {size wk m t : Nat}
    [NeZero m] {B : Fin m} {tab : List Nat}
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hT : TabLay P wk tab) (ops : List TabOp) {s : State} {v v' : Nat × List Nat}
    (hr : tabRun ops v = some v')
    (I : PowerState P base size m B v.1 t s) (TO : TabOk P base m B tab v.2 s.mem) :
    WP isa (tabChain P F tab ops) s fun u =>
      PowerState P base size m B v'.1 t u ∧ TabOk P base m B tab v'.2 u.mem ∧
      Keeps powClob s u ∧ Unch base (powWx P wk ++ tabW P tab) s.mem u.mem := by
  induction ops generalizing s v with
  | nil =>
    cases Option.some.inj hr
    exact WP.block_nil ⟨I, TO, Keeps.refl .., Unch.refl base _ s.mem⟩
  | cons op ops ih =>
    simp only [tabRun] at hr
    cases h1 : tabStep op v with
    | none => rw [h1] at hr; exact absurd hr (by simp)
    | some v₁ =>
      rw [h1, Option.bind_some] at hr
      refine WP.seq (WP.mono (tabOp_ok hL hW hm hT op h1 I TO) fun u ⟨Iu, Tu, Ku, Uu⟩ => ?_)
      exact WP.mono (ih hr Iu Tu) fun w ⟨Iw, Tw, Kw, Uw⟩ =>
        ⟨Iw, Tw, Ku.trans Kw, fun x hx => (Uw x hx).trans (Uu x hx)⟩

/-- A sequence from the base: `[acc]` reads as the base to the exponent the
sequence reaches. -/
theorem tabPower_ok {P : PowCfg} {F : Impl.Weierstrass.Mont.Modulus} {base : Addr} {size wk m : Nat}
    [NeZero m] {tab : List Nat}
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hT : TabLay P wk tab) (ops : List TabOp) {e : Nat} {T : List Nat}
    (he : tabRun ops (1, List.replicate tab.length 0) = some (e, T))
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m) :
    WP isa (tabPower P F tab ops) s fun u => Keeps powClob s u ∧
      Unch base (powWx P wk ++ tabW P tab) s.mem u.mem ∧
      wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  refine WP.seq (WP.mono (powerInit_ok hL hW hs hM hB) fun s₁ ⟨I₁, K₁, U₁⟩ => ?_)
  have T₁ : TabOk P base m (toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n)) tab
      (List.replicate tab.length 0) s₁.mem :=
    ⟨List.length_replicate, fun i hi h0 => absurd (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl) h0⟩
  refine WP.mono (tabChain_ok hL hW hm hT ops he I₁ T₁) fun u ⟨Iu, _, Ku, Uu⟩ => ?_
  exact ⟨(K₁.mono (by decide)).trans Ku,
    fun x hx => (Uu x hx).trans (U₁ x fun w hw => hx w (List.mem_append_left _ hw)),
    Iu.acc_lt, Iu.acc_val⟩

/-- The power `e` by a sliding window, for any `e` that is not zero. -/
theorem windowPower_ok {P : PowCfg} {F : Impl.Weierstrass.Mont.Modulus} {base : Addr} {size wk m : Nat}
    [NeZero m] {tab : List Nat}
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hT : TabLay P wk tab) (hlen : tab.length = 9) {e bits : Nat} (h0 : 0 < e) (he : e < 2 ^ bits)
    (hb : bits + 4 < 2 ^ 32)
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m) :
    WP isa (tabPower P F tab (windowOps e bits)) s fun u => Keeps powClob s u ∧
      Unch base (powWx P wk ++ tabW P tab) s.mem u.mem ∧
      wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e :=
  tabPower_ok hL hW hm hT _ (by rw [hlen]; exact windowOps_run h0 he hb) hs hM hB

end VG.Proof.Weierstrass.X86
