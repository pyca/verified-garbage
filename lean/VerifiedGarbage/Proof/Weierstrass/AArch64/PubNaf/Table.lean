module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# The public NAF's table

`E = 2P`, then `R = P`, stored in the first entry, and seven times `R = R + E`
stored in the next (`table_ok`): the table holds `[1]P, [3]P, …, [15]P`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `3 n` words copied give each coordinate of `n` words. -/
theorem coord_words {m m' : Mem} {base : Addr} {dst src n c : Nat} (hc : c < 3)
    (h : ∀ i < 3 * n, word m' base (dst + 8 * i) = word m base (src + 8 * i)) :
    wordsVal m' base (dst + 8 * n * c) n = wordsVal m base (src + 8 * n * c) n := by
  apply wordsVal_of_words₂
  intro i hi
  have he := h (n * c + i) (by
    have : n * c + i < n * c + n := by omega
    have : n * c + n ≤ 3 * n := by rw [← Nat.mul_succ, Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ hc
    omega)
  rw [show dst + 8 * (n * c + i) = dst + 8 * n * c + 8 * i by rw [Nat.mul_add, Nat.mul_assoc]; omega,
    show src + 8 * (n * c + i) = src + 8 * n * c + 8 * i by rw [Nat.mul_add, Nat.mul_assoc]; omega] at he
  exact he

/-- What a copy of `3 n` words from `o` changes, as the three coordinates' slots. -/
theorem unch_of_outside {base : Addr} {m m' : Mem} {o n : Nat}
    (h : Outside base o (8 * (3 * n)) m m') :
    Unch base [(o, 8 * n), (o + 8 * n, 8 * n), (o + 8 * n * 2, 8 * n)] m m' := by
  intro x hx
  apply h x
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  omega

/-- The bounds of entry `a`'s slots. -/
theorem tbl_le {K : WinCfg} {size : Nat} (hL : WinLay K size) {i : Nat} (hi : i < 24) :
    K.tbl + 8 * K.M.n * i + 8 * K.M.n ≤ size :=
  hL.lay.le _ (by simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

theorem tbl8 {K : WinCfg} (hA : WinA K) : K.tbl % 8 = 0 := by
  have := hA.sl K.tbl (by
    simp only [winSlots, List.mem_append]
    exact Or.inr (by simpa using winTbl_mem K (i := 0) (by decide)))
  exact this

/-- `R` into entry `m + 1`, through `x20 = base + stride m`. -/
theorem store_ok {K : WinCfg} {size : Nat} (hL : NafLay K size) {s : State} {base : Addr} {m : Nat}
    (hs : Scr s base size) (hm : m < 8) (h20 : s.gpr .x20 = off base (stride K * m)) :
    WP isa (.block (store K)) s fun t =>
      (∀ c < 3, wordsVal t.mem base (K.tbl + 8 * K.M.n * (3 * m + c)) K.M.n =
        wordsVal s.mem base (K.R.x + 8 * K.M.n * c) K.M.n) ∧ KeepRegs [.x4] s t ∧
      Unch base [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
        ((K.tblPt (m + 1)).z, 8 * K.M.n)] s.mem t.mem := by
  have hW := hL.win
  have hn0 := hW.n0
  have hRx : K.R.x ∈ winOther K := by win_in
  have hRz : K.R.z ∈ winOther K := by win_in
  have tx := hW.tbl K.R.x (List.mem_append_right _ hRx)
  have tz := hW.tbl K.R.z (List.mem_append_right _ hRz)
  have rz := hW.lay.le K.R.z (winOther_mem hRz)
  have r8 := hL.al.sl K.R.x (winOther_mem hRx)
  have t8 := tbl8 hL.al
  have hle := tbl_le hW (i := 3 * m + 2) (by omega)
  have rxz := hL.rxz
  have hst : stride K = 24 * K.M.n := rfl
  rw [rxz] at tz rz
  have hmul : 8 * K.M.n * (3 * m + 2) = 24 * K.M.n * m + 16 * K.M.n := by grind
  have hm8 : 24 * K.M.n * m + 24 * K.M.n ≤ 24 * K.M.n * 8 := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hm
  refine WP.mono (stOff_ok hs h20 (o := K.tbl) (src := K.R.x) (n := 3 * K.M.n) t8
    (by rw [hst]; omega) (by omega) r8 (by rw [hst]; omega) (3 * K.M.n) (Nat.le_refl _))
    fun t ⟨e, k, O⟩ => ⟨fun c hc => ?_, k, ?_⟩
  · have := coord_words (n := K.M.n) hc (dst := stride K * m + K.tbl) (src := K.R.x) e
    rw [← this]
    congr 1
    rw [hst]; grind
  · have U := unch_of_outside O
    refine U.mono fun w hw => ?_
    simp only [WinCfg.tblPt, Nat.add_sub_cancel, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rw [hst] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (by congr 1; omega)
    · exact Or.inr (Or.inl (by congr 1; omega))
    · exact Or.inr (Or.inr (by congr 1; omega))

/-! ## The construction -/

/-- The construction after `m` entries, from `s₀`: `R = [2m - 1]P`, `E = 2P`,
`x20` at entry `m + 1`. -/
structure TSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State)
    (m : Nat) : Prop where
  scr : Scr s base size
  keep : KeepRegs (nafClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : OddTbl K C base P m s
  elt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p
  e2 : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)
    (mul 2 P)
  rlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  r : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (2 * m - 1) P)
  x20 : s.gpr .x20 = off base (stride K * m)

theorem mem3 {a b c x : Nat} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem R_other (K : WinCfg) : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K :=
  pt_other (Or.inl rfl)
theorem D_other (K : WinCfg) : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winOther K :=
  pt_other (Or.inr (Or.inl rfl))
theorem E_other (K : WinCfg) : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K :=
  pt_other (Or.inr (Or.inr rfl))

/-- Slots of the window method, below `p`, and the field programs' invariant. -/
theorem inv_of {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base) {V : List Nat}
    (hsl : ∀ x ∈ V, x ∈ winSlots K) (hlt : ∀ x ∈ V, wordsVal s.mem base x K.M.n < C.p) :
    Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
  ⟨hs, hM, hsl, hlt, fun _ _ => rfl⟩

/-- A slot written by the loop keeps its number through what the loop writes elsewhere. -/
theorem words_keep {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {m m' : Mem}
    {W : List Nat} (hU : Unch base (W.map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]) m m')
    (hW : ∀ y ∈ W, y ∈ winSlots K) {x : Nat} (hx : x ∈ winSlots K) (hxW : x ∉ W)
    (hn : base.toNat + size ≤ 2 ^ 64) :
    wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; omega)
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hx (hW y hy) (fun e => hxW (e ▸ hy))
  · exact hL.lay.tmp x hx

theorem winRo_lt {K : WinCfg} {C : Curve} {size k : Nat} (hL : WinLay K size) {base : Addr}
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) (hU : Unch base (winW K) s₀.mem s.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : ∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p :=
  fun x hx => by rw [hL.ro_val hU hn hx]; exact hF.ro_lt x hx

/-- `D = R + E` (`[2m - 1]P + 2P`), then `R = D`. -/
theorem tableAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ : State} (hF : NafFixed K C base s₀ P k)
    {m : Nat} (hm1 : 1 ≤ m) {s : State} (h : TSt K C base size P s₀ s m) :
    WP isa (.seq (Jacobian.jacAdd K K.R K.E K.D) (.block (copyPt K.M.n K.R K.D))) s fun t =>
      Scr t base size ∧ KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n) ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z)
        (mul (2 * (m + 1) - 1) P) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have ro := winRo_lt hW hF h.unch hn
  obtain ⟨-, -, -, a4, -, a6, -, -⟩ := rcbApart_naf hW
  have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  have sD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (D_other K x hx)
  have sl := winJ_sl (o := K.D) (p := K.R) (q := K.E) (D_other K) sR sE
  let V := winRo K ++ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z]
  have hVs : ∀ x ∈ V, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h <;> subst h <;> win_in
  have hVl : ∀ x ∈ V, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ro x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' <;> subst h'
      · exact h.rlt _ (by simp)
      · exact h.rlt _ (by simp)
      · exact h.rlt _ (by simp)
      · exact h.elt _ (by simp)
      · exact h.elt _ (by simp)
      · exact h.elt _ (by simp)
  have hRV : ∀ x ∈ rcbR K.S K.R K.E, x ∈ V := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
  refine WP.seq (WP.mono (jacAddB_ok hW.lay hL.al.al hL.n4 hp hC hM3 a6 sl.1 (hL.al.low sl.2.2)
    (inv_of h.scr h.mod hVs hVl) hRV hone (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) h.r h.e2)
    fun s₁ h₁ => ?_)
  obtain ⟨sc₁, k₁, U₁, M₁, dlt, dJ, Vlt, Veq⟩ :=
    jacPost_frame hW h.scr h.mod (Or.inr (Or.inl rfl)) h₁
  rw [hC.add_mul_mul hP] at dJ
  have hEW : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := fun x hx =>
    a6.apart x (by simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h <;> simp [h])
  have E₁ : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => Veq x (List.mem_append_right _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])) (hEW x hx)
  -- `R = D`.
  let V₁ := winRo K ++ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]
  have hV₁s : ∀ x ∈ V₁, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h <;> subst h <;> win_in
  have hV₁l : ∀ x ∈ V₁, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Vlt x (List.mem_append_left _ hx)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' <;> subst h'
      · exact dlt _ (by simp)
      · exact dlt _ (by simp)
      · exact dlt _ (by simp)
      · exact Vlt _ (by simp [V])
      · exact Vlt _ (by simp [V])
      · exact Vlt _ (by simp [V])
  have sl₁ := winJ_sl (o := K.R) (p := K.E) (q := K.D) (R_other K) sE sD
  have hRV₁ : ∀ x ∈ rcbR K.S K.E K.D, x ∈ V₁ := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V₁, winRo]
  refine WP.mono (copyPointJ_ok hW.lay hL.al.al a4 sl₁.1 (inv_of sc₁ M₁ hV₁s hV₁l) hRV₁ dJ)
    fun t h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, rlt₂, rJ₂, -, V₁eq⟩ := jacPost_frame hW sc₁ M₁ (Or.inl rfl) h₂
  have hER : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.R := fun x hx =>
    a4.apart x (by simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h <;> simp [h])
  refine ⟨sc₂, k₁.trans k₂, (U₁.trans U₂).mono (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw), M₂, fun x hx => ?_, rlt₂, ?_⟩
  · rw [V₁eq x (List.mem_append_right _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])) (hER x hx), E₁ x hx]
  · rw [show 2 * (m + 1) - 1 = 2 * m - 1 + 2 by omega]
    exact rJ₂

/-- A slot but entry `j`'s keeps its number through a store into entry `j`. -/
theorem entry_unch {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {j : Nat}
    (hj1 : 1 ≤ j) (hj8 : j ≤ 8) {m m' : Mem}
    (hU : Unch base [((K.tblPt j).x, 8 * K.M.n), ((K.tblPt j).y, 8 * K.M.n),
      ((K.tblPt j).z, 8 * K.M.n)] m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat}
    (hx : x ∈ winSlots K) (hxj : x ∉ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z]) :
    wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; omega)
  have hy : w.1 ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z] ∧ w.2 = 8 * K.M.n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp
  obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K hj1 hj8 _ hy.1
  have hs : w.1 ∈ winSlots K := by
    rw [e]; simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
  rw [hy.2]
  exact hL.lay.apart x w.1 hx hs (fun h => hxj (h ▸ hy.1))

theorem tbl_slot {K : WinCfg} {a : Nat} (h1 : 1 ≤ a) (h8 : a ≤ 8) :
    ∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z], x ∈ winSlots K := by
  intro x hx
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
  simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)

/-- A point written by the loop is not in the table. -/
theorem other_not_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {a : Nat} (h1 : 1 ≤ a)
    (h8 : a ≤ 8) {x : Nat} (hx : x ∈ winRo K ++ winOther K) :
    x ∉ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z] := fun h => by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x h
  exact hL.tbl_ne hx hi rfl

/-- Entries `a ≠ j` are apart. -/
theorem tbl_not_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {a j : Nat} (ha1 : 1 ≤ a)
    (ha8 : a ≤ 8) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (h : a ≠ j) {x : Nat}
    (hx : x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z]) :
    x ∉ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z] := fun h' => by
  obtain ⟨i, hi, rfl, hia, hia'⟩ := tblPt_mem K ha1 ha8 _ hx
  obtain ⟨i', hi', e, hij, hij'⟩ := tblPt_mem K hj1 hj8 _ h'
  have : i ≠ i' := by
    intro hii; subst hii
    have : a - 1 < j ∧ j - 1 < a := by omega
    omega
  exact hL.tbl_ne₂ this e

/-- An iteration of the construction: entry `m + 1` is `[2m + 1]P`. -/
theorem tableStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ : State} (hF : NafFixed K C base s₀ P k)
    {m : Nat} (hm1 : 1 ≤ m) (hm : m < 8) {s : State} (h : TSt K C base size P s₀ s m)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (8 - m)) :
    WP isa (tableStep K) s fun t =>
      TSt K C base size P s₀ t (m + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1)) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have h10 : K.M.n < 10 := by have := hL.n6; omega
  rw [tableStep]
  refine WP.seq (WP.mono (tableAdd_ok hL hp hC hM3 hone hP hF hm1 h)
    fun s₂ ⟨sc₂, k₂, U₂, M₂, E₂, rlt₂, rJ₂⟩ => ?_)
  have x20₂ : s₂.gpr .x20 = off base (stride K * m) := (k₂.gpr _ (x20_not_clob' h10)).trans h.x20
  have x19₂ : s₂.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₂.gpr _ (x19_not_clob _)).trans h19
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hL sc₂ hm x20₂) fun s₃ ⟨cw, k₃, U₃⟩ => ?_
  have sc₃ := sc₂.of_keepRegs k₃ (by decide)
  have x20₃ : s₃.gpr .x20 = off base (stride K * m) := (k₃.gpr _ (by decide)).trans x20₂
  have x19₃ : s₃.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₃.gpr _ (by decide)).trans x19₂
  rw [show ([.addImm .x .x20 .x20 (stride K), decCounter] : List Instr) =
    [.addImm .x .x20 .x20 (stride K)] ++ [decCounter] from rfl, WP.block_append_iff]
  have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega
  refine WP.mono (addImm_ok s₃ (d := .x20) (n := .x20) hst) fun s₄ ⟨a₄, k₄⟩ => ?_
  have sc₄ := sc₃.of_keeps k₄ (by decide)
  have x19₄ : s₄.gpr .x19 = BitVec.ofNat 64 (8 - m) := (k₄.gpr _ (by decide)).trans x19₃
  refine WP.mono (decCounter_ok s₄ (by omega) (by omega) x19₄) fun t ⟨x19t, kt⟩ => ?_
  have sct := sc₄.of_keeps kt (by decide)
  have m34 : t.mem = s₃.mem := by rw [kt.mem, k₄.mem]
  have U3' := fun {x : Nat} => entry_unch hW (j := m + 1) (by omega) (by omega) U₃ hn (x := x)
  have keepS : ∀ x ∈ winRo K ++ winOther K,
      wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := fun x hx => by
    rw [m34]
    exact U3' (by
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · exact winOther_mem hx) (other_not_tbl hW (by omega) (by omega) hx)
  have tm : ∀ x ∈ winRo K ++ winOther K, tmv C K.M.n base t x = tmv C K.M.n base s₂ x :=
    fun x hx => by show toM _ _ _ = toM _ _ _; rw [keepS x hx]
  have oR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have oE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  -- The table.
  have T₂ : OddTbl K C base P m s₂ := h.tbl.unch hW (by omega) U₂ hn
  have hU3w : Unch base (winW K) s₂.mem t.mem := by
    rw [m34]
    refine U₃.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, List.mem_append_right _ ?_, by rcases hw with rfl | rfl | rfl <;> rfl⟩
    obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega) (by omega) w.1 (by
      rcases hw with rfl | rfl | rfl <;> simp)
    rw [e]; exact winTbl_mem K hi
  refine ⟨⟨sct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h.keep.trans ((k₂.mono clob_nafClob).trans ((k₃.mono (fun r hr => nafClob_mem (by
      simp only [List.mem_singleton] at hr; subst hr; simp))).trans
      ((Keeps.regs k₄).mono (fun r hr => nafClob_mem (by
        simp only [List.mem_singleton] at hr; subst hr; simp)) |>.trans
      ((Keeps.regs kt).mono (fun r hr => nafClob_mem (by
        simp only [List.mem_singleton] at hr; subst hr; simp))))))
  · exact ((h.unch.trans U₂).trans hU3w).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · exact hw
      · exact loopW_sub K w hw
      · exact hw
  · exact M₂.unch hU3w (fun w hw => winW_mo hW M₂ w hw) hn
  · intro a ha1 ham
    rcases Nat.lt_or_ge a (m + 1) with ha | ha
    · obtain ⟨tl, tJ⟩ := T₂ a ha1 (by omega)
      have e : ∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z],
          wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := fun x hx => by
        rw [m34]
        exact U3' (tbl_slot ha1 (by omega) x hx) (tbl_not_tbl hW ha1 (by omega) (by omega) (by omega)
          (by omega) hx)
      refine ⟨fun x hx => by rw [e x hx]; exact tl x hx, ?_⟩
      have et : ∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z],
          tmv C K.M.n base t x = tmv C K.M.n base s₂ x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [et _ (by simp), et _ (by simp), et _ (by simp)]
      exact tJ
    · obtain rfl : a = m + 1 := by omega
      have ec : ∀ c < 3, wordsVal t.mem base (K.tbl + 8 * K.M.n * (3 * m + c)) K.M.n =
          wordsVal s₂.mem base (K.R.x + 8 * K.M.n * c) K.M.n := fun c hc => by rw [m34]; exact cw c hc
      have px : (K.tblPt (m + 1)).x = K.tbl + 8 * K.M.n * (3 * m + 0) := by
        rw [tblPt_x]; congr 2
      have py : (K.tblPt (m + 1)).y = K.tbl + 8 * K.M.n * (3 * m + 1) := by
        rw [tblPt_y, Nat.add_sub_cancel]
      have pz : (K.tblPt (m + 1)).z = K.tbl + 8 * K.M.n * (3 * m + 2) := by
        rw [tblPt_z, Nat.add_sub_cancel]
      have rx : K.R.x = K.R.x + 8 * K.M.n * 0 := by simp
      have ry : K.R.y = K.R.x + 8 * K.M.n * 1 := by rw [hL.rxy]; simp
      have rz : K.R.z = K.R.x + 8 * K.M.n * 2 := by rw [hL.rxz]; omega
      have ex := ec 0 (by decide)
      have ey := ec 1 (by decide)
      have ez := ec 2 (by decide)
      rw [← px, ← rx] at ex
      rw [← py, ← ry] at ey
      rw [← pz, ← rz] at ez
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases mem3 hx with rfl | rfl | rfl
        · rw [ex]; exact rlt₂ _ (by simp)
        · rw [ey]; exact rlt₂ _ (by simp)
        · rw [ez]; exact rlt₂ _ (by simp)
      · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [ex, ey, ez]
        exact rJ₂
  · intro x hx; rw [keepS x (oE x hx), E₂ x hx]; exact h.elt x hx
  · have e : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base t x = tmv C K.M.n base s x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [keepS x (oE x hx), E₂ x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact h.e2
  · intro x hx; rw [keepS x (oR x hx)]; exact rlt₂ x hx
  · rw [tm _ (oR _ (by simp)), tm _ (oR _ (by simp)), tm _ (oR _ (by simp))]; exact rJ₂
  · rw [kt.gpr _ (by decide), a₄, x20₃]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
  · rw [x19t]; congr 1

theorem add_self_mul {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P = true) :
    Spec.Weierstrass.add P P = mul 2 P := by
  have := hC.add_mul_mul hP 1 1
  rw [mul_one_pt] at this
  exact this

/-- `E = 2P`, `R = P` into entry 1, `x20` at entry 2, `x19 = 7`. -/
theorem tableInit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    {P : Point C} (hP : onCurve C P = true) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkA K.M size C.p s₀.mem base) (hF : NafFixed K C base s₀ P k) :
    WP isa (.seq (fprogB K.M (dblJ K.S K.P K.E)) (.block (copyPt K.M.n K.R K.P ++
      ([.addImm .x .x20 .x0 0] : List Instr) ++ store K ++
      ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr))))
      s₀ fun t => TSt K C base size P s₀ t 1 ∧ t.gpr .x19 = BitVec.ofNat 64 7 := by
  have hW := hL.win
  have hn := hs.nowrap
  obtain ⟨a1, -, a3, -, -, -, -, -⟩ := rcbApart_naf hW
  have sP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K ++ winOther K := by
    intro x hx; apply List.mem_append_left
    rcases mem3 hx with rfl | rfl | rfl <;> simp [winRo]
  have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  have sl := winJ_sl (o := K.E) (p := K.P) (q := K.P) (E_other K) sP sP
  have hPV : ∀ x ∈ rcbR K.S K.P K.P, x ∈ winRo K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [winRo]
  have hd := dblB_ok false hW.lay hL.al.al hp hC hM3 a1 sl.1 (hL.al.low sl.2.2)
    (inv_of hs hM (winRo_slots K) hF.ro_lt) hPV hP hF.pt
  simp only [Bool.false_eq_true, ite_false] at hd
  refine WP.seq (WP.mono hd fun s₁ h₁ => ?_)
  obtain ⟨sc₁, k₁, U₁, M₁, elt₁, eJ₁, rolt₁, roeq₁⟩ := jacPost_frame hW hs hM (Or.inr (Or.inr rfl)) h₁
  rw [add_self_mul hC hP] at eJ₁
  have hroE : ∀ x ∈ winRo K, x ∉ rcbW K.S K.E := fun x hx h =>
    hW.ro x hx (rcbW_other (Or.inr (Or.inr rfl)) x h)
  have Pv₁ : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx
    have hx' : x ∈ winRo K := by rcases mem3 hx with rfl | rfl | rfl <;> simp [winRo]
    show toM _ _ _ = toM _ _ _; rw [roeq₁ x hx' (hroE x hx')]
  -- `R = P`.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  let V₁ := winRo K ++ [K.E.x, K.E.y, K.E.z]
  have hV₁s : ∀ x ∈ V₁, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (E_other K x hx)
  have hV₁l : ∀ x ∈ V₁, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact rolt₁ x hx
    · exact elt₁ x hx
  have sl₁ := winJ_sl (o := K.R) (p := K.E) (q := K.P) (R_other K) sE sP
  have hRV₁ : ∀ x ∈ rcbR K.S K.E K.P, x ∈ V₁ := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [V₁, winRo]
  have pJ : InvJ C (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y)
      (tmv C K.M.n base s₁ K.P.z) P := by
    rw [Pv₁ _ (by simp), Pv₁ _ (by simp), Pv₁ _ (by simp)]; exact hF.pt
  refine WP.mono (copyPointJ_ok hW.lay hL.al.al a3 sl₁.1 (inv_of sc₁ M₁ hV₁s hV₁l) hRV₁ pJ)
    fun s₂ h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, rlt₂, rJ₂, V₁lt, V₁eq⟩ := jacPost_frame hW sc₁ M₁ (Or.inl rfl) h₂
  have hER : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.R := fun x hx =>
    a3.apart x (by simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h <;> simp [h])
  have E₂ : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n :=
    fun x hx => V₁eq x (List.mem_append_right _ hx) (hER x hx)
  -- `x20 = base`.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok s₂ (d := .x20) (n := .x0) (imm := 0) (by decide)) fun s₃ ⟨a₃, k₃⟩ => ?_
  have sc₃ := sc₂.of_keeps k₃ (by decide)
  have x20₃ : s₃.gpr .x20 = off base (stride K * 0) := by
    rw [a₃, sc₂.x0]; simp [off]
  -- Entry 1.
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hL sc₃ (m := 0) (by decide) x20₃) fun s₄ ⟨cw, k₄, U₄⟩ => ?_
  have sc₄ := sc₃.of_keepRegs k₄ (by decide)
  rw [show ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr) =
    [.addImm .x .x20 .x20 (stride K)] ++ [.movz .x .x19 (BitVec.ofNat 16 7) 0] from rfl,
    WP.block_append_iff]
  have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega
  refine WP.mono (addImm_ok s₄ (d := .x20) (n := .x20) hst) fun s₅ ⟨a₅, k₅⟩ => ?_
  have sc₅ := sc₄.of_keeps k₅ (by decide)
  refine WP.mono (setCounter_ok s₅ (j := 7) (by decide)) fun t ⟨x19t, kt⟩ => ?_
  have sct := sc₅.of_keeps kt (by decide)
  have m4 : t.mem = s₄.mem := by rw [kt.mem, k₅.mem]
  have m3 : s₃.mem = s₂.mem := k₃.mem
  have U4' := fun {x : Nat} => entry_unch hW (j := 0 + 1) (by omega) (by omega) U₄ hn (x := x)
  have keepS : ∀ x ∈ winRo K ++ winOther K,
      wordsVal t.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := fun x hx => by
    rw [m4, U4' (by
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · exact winOther_mem hx) (other_not_tbl hW (by omega) (by omega) hx), m3]
  have tm : ∀ x ∈ winRo K ++ winOther K, tmv C K.M.n base t x = tmv C K.M.n base s₂ x :=
    fun x hx => by show toM _ _ _ = toM _ _ _; rw [keepS x hx]
  have oR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have hU4w : Unch base (winW K) s₂.mem t.mem := by
    rw [m4, ← m3]
    refine U₄.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, List.mem_append_right _ ?_, by rcases hw with rfl | rfl | rfl <;> rfl⟩
    obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := 0 + 1) (by omega) (by omega) w.1 (by
      rcases hw with rfl | rfl | rfl <;> simp)
    rw [e]; exact winTbl_mem K hi
  have kc : ∀ r ∈ [Reg.x20], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have kc4 : ∀ r ∈ [Reg.x4], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have kc19 : ∀ r ∈ [Reg.x19], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have K12 := (k₁.mono clob_nafClob).trans (k₂.mono clob_nafClob)
  have K3 := (Keeps.regs k₃).mono kc
  have K4 := k₄.mono kc4
  have K5 := (Keeps.regs k₅).mono kc
  have Kt := (Keeps.regs kt).mono kc19
  refine ⟨⟨sct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, x19t⟩
  · exact K12.trans (K3.trans (K4.trans (K5.trans Kt)))
  · exact ((U₁.trans U₂).trans hU4w).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · exact loopW_sub K w hw
      · exact loopW_sub K w hw
      · exact hw
  · exact M₂.unch hU4w (fun w hw => winW_mo hW M₂ w hw) hn
  · intro a ha1 ha
    obtain rfl : a = 1 := by omega
    have ec : ∀ c < 3, wordsVal t.mem base (K.tbl + 8 * K.M.n * (3 * 0 + c)) K.M.n =
        wordsVal s₂.mem base (K.R.x + 8 * K.M.n * c) K.M.n := fun c hc => by
      rw [m4, cw c hc, m3]
    have ex := ec 0 (by decide)
    have ey := ec 1 (by decide)
    have ez := ec 2 (by decide)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one] at ex ey ez
    rw [show K.tbl + 8 * K.M.n * 2 = (K.tblPt 1).z by simp [WinCfg.tblPt]; omega,
      show K.R.x + 8 * K.M.n * 2 = K.R.z by rw [hL.rxz]; omega] at ez
    rw [show K.tbl + 8 * K.M.n = (K.tblPt 1).y by simp [WinCfg.tblPt],
      show K.R.x + 8 * K.M.n = K.R.y by rw [hL.rxy]] at ey
    rw [show K.tbl = (K.tblPt 1).x by simp [WinCfg.tblPt]] at ex
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases mem3 hx with rfl | rfl | rfl
      · rw [ex]; exact rlt₂ _ (by simp)
      · rw [ey]; exact rlt₂ _ (by simp)
      · rw [ez]; exact rlt₂ _ (by simp)
    · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [ex, ey, ez, show 2 * 1 - 1 = 1 from rfl, mul_one_pt]
      exact rJ₂
  · intro x hx; rw [keepS x (sE x hx), E₂ x hx]; exact elt₁ x hx
  · have e : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base t x = tmv C K.M.n base s₁ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [keepS x (sE x hx), E₂ x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact eJ₁
  · intro x hx; rw [keepS x (oR x hx)]; exact rlt₂ x hx
  · rw [tm _ (oR _ (by simp)), tm _ (oR _ (by simp)), tm _ (oR _ (by simp)),
      show 2 * 1 - 1 = 1 from rfl, mul_one_pt]
    exact rJ₂
  · rw [kt.gpr _ (by decide), a₅, k₄.gpr _ (by decide), x20₃]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_zero, Nat.zero_add, Nat.mul_one]

/-- The table: entries `1 … 8` hold `[1]P, [3]P, …, [15]P`. -/
theorem table_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkA K.M size C.p s₀.mem base) (hF : NafFixed K C base s₀ P k) :
    WP isa (table K) s₀ fun t => NSt K C base size P s₀ t := by
  rw [table]
  apply WP.assoc
  refine WP.seq (WP.mono (tableInit_ok hL hp hC hM3 hP hs hM hF) fun s₁ ⟨T₁, x19₁⟩ => ?_)
  refine countLoop_ok (Inv := fun j t => TSt K C base size P s₀ t (8 - j) ∧ t.gpr .x19 = BitVec.ofNat 64 j)
    (n := 7) (by decide) (fun j t hj1 hj7 hI => ?_)
    (fun t hI => ⟨hI.1.scr, hI.1.keep, hI.1.unch, hI.1.mod, hI.1.tbl⟩) (by decide) ⟨by simpa using T₁, x19₁⟩
  have e : 8 - (8 - j) = j := by omega
  refine WP.mono (tableStep_ok hL hp hC hM3 hone hP hF (m := 8 - j) (by omega) (by omega) hI.1
    (by rw [e]; exact hI.2)) fun t' ⟨T', x'⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show 8 - (j - 1) = 8 - j + 1 by omega]; exact T'
  · rw [x']; congr 1; omega
  · rw [x']; congr 1; omega

end VG.Proof.Weierstrass.AArch64.PubNaf
