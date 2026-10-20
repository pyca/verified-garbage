module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# The public NAF's table

What the table's construction (`TableCoZ.lean`) shares: the stores into its
entries, and the slots they keep.
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

theorem add_self_mul {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P = true) :
    Spec.Weierstrass.add P P = mul 2 P := by
  have := hC.add_mul_mul hP 1 1
  rw [mul_one_pt] at this
  exact this

end VG.Proof.Weierstrass.AArch64.PubNaf
