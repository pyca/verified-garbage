import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJBuild
import VerifiedGarbage.Proof.Weierstrass.WindowJA
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-!
# Windows in Jacobian coordinates on x86-64: the table into affine coordinates

`normTbl` (Montgomery's trick) on the table `build` leaves (`TblOk`): the
prefix products `c_m = Z_1 ⋯ Z_m` (`prod_ok`), `c_8^(p-2)` by the inversion,
then back from entry `8` (`back_ok`): `Z_m^(p-2) = c_m^(p-2) c_{m-1}` and
`c_{m-1}^(p-2) = c_m^(p-2) Z_m` (`trick_step`), each entry's `X` and `Y` by its
`Z^(p-2)`, and every `Z` set to one: a table of `RepA` (`normTbl_ok`), for
entries other than `O`. Each product is `slotMul_ok`, on the window's slots.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- One product on the window's slots, writing a slot written: the other
slots keep their numbers. -/
theorem slotMul_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) {o a b : Nat} (ho : o ∈ winWs K) (ha : a ∈ winSlots K)
    (hb : b ∈ winSlots K) (hla : wordsVal s.mem base a K.M.n < C.p)
    (hlb : wordsVal s.mem base b K.M.n < C.p) :
    WP isa (opProg K.M (.mul o a b)).inline s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (winW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ winSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  have I : Inv K.M base size C.p (· ∈ winSlots K) [a, b] (tmv C K.M.n base s) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hla
      · exact hlb
  have hSo : o ∈ winSlots K := winWs_slots K o ho
  refine WP.mono (opProg_ok hL.lay hp I (op := .mul o a b) (fun x hx => by
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hSo
      · exact ha
      · exact hb)
    (fun x hx => hx)) fun s' ⟨k, I'⟩ => ?_
  have U : Unch base [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem :=
    fun x hx => k.mem x (hx _ (List.mem_cons_self ..)) (hx (K.M.tmp, 8 * K.M.n) (by simp))
  refine ⟨I'.scr, ⟨k.gpr, k.rd, k.wr⟩, U.mono fun w hw => ?_, I'.mod, I'.lt o (List.mem_cons_self ..),
    ?_, fun x hx hxo => U.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; have := hs.nowrap; omega_arith)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl
    · exact Or.inl ⟨o, ho, rfl⟩
    · exact Or.inr rfl
  · have v := I'.val o (List.mem_cons_self ..)
    simp only [FOp.run, Function.update_self] at v
    exact v
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hL.lay.apart x o hx hSo hxo
    · exact hL.lay.tmp x hx

theorem fprog_append (M : Mod) (a b : List FOp) : fprog M (a ++ b) = fprog M a ++ fprog M b := by
  simp only [fprog, List.flatMap_append]

/-- Straight-line code made of `N` pieces, by an invariant of the pieces done. -/
theorem block_range_ok {f : Nat → List Instr} {N : Nat} {Inv : Nat → State → Prop}
    (step : ∀ i < N, ∀ s, Inv i s → WP isa (.block (f i)) s (Inv (i + 1))) :
    ∀ i ≤ N, ∀ s, Inv 0 s → WP isa (.block ((List.range i).flatMap f)) s (Inv i)
  | 0, _, s, h => by simpa using (WP.block_nil h : WP isa (.block []) s (Inv 0))
  | i + 1, hi, s, h => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (block_range_ok step i (by omega_arith) s h) fun t ht => ?_
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using step i (by omega_arith) t ht

/-! ## The slots of the prefix products -/

/-- The slots holding `c_2 … c_8`, then `D.x` and `E.x`: written, and distinct. -/
def normW (K : WinCfg) : List Nat :=
  [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.R.z, K.D.x, K.E.x]

theorem normW_other (K : WinCfg) : ∀ x ∈ normW K, x ∈ winOther K := by
  intro x hx
  simp only [normW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem

theorem normW_nodup {K : WinCfg} {size : Nat} (hL : WinLay K size) : (normW K).Nodup := by
  have hnd := hL.nodup
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  simp only [normW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  grind

theorem prodSl_eq (K : WinCfg) {j : Nat} (h2 : 2 ≤ j) (h8 : j ≤ 8) :
    WinCfg.prodSl K j = (normW K)[j - 2]'(by simp [normW]; omega_arith) := by
  rcases (show j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem prodSl_one (K : WinCfg) : WinCfg.prodSl K 1 = (K.tblPt 1).z := rfl

theorem prodSl_other {K : WinCfg} {j : Nat} (h2 : 2 ≤ j) (h8 : j ≤ 8) : WinCfg.prodSl K j ∈ winOther K := by
  rw [prodSl_eq K h2 h8]; exact normW_other K _ (List.getElem_mem ..)

theorem normW_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) {i i' : Nat} (hi : i < (normW K).length)
    (hi' : i' < (normW K).length) (h : i ≠ i') : (normW K)[i] ≠ (normW K)[i'] := by
  have hp := List.pairwise_iff_getElem.mp (normW_nodup hL)
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact hp i i' hi hi' h
  · exact fun e => hp i' i hi' hi h e.symm

theorem prodSl_inj {K : WinCfg} {size : Nat} (hL : WinLay K size) {j j' : Nat} (h2 : 2 ≤ j) (h8 : j ≤ 8)
    (h2' : 2 ≤ j') (h8' : j' ≤ 8) (h : WinCfg.prodSl K j = WinCfg.prodSl K j') : j = j' := by
  rw [prodSl_eq K h2 h8, prodSl_eq K h2' h8'] at h
  exact Classical.byContradiction fun hne => normW_ne hL _ _ (by omega_arith) h

/-- `D.x` and `E.x` are not the slots of `c_2 … c_7`. -/
theorem prodSl_ne_DE {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (h2 : 2 ≤ j) (h7 : j ≤ 8) :
    WinCfg.prodSl K j ≠ K.D.x ∧ WinCfg.prodSl K j ≠ K.E.x := by
  rw [prodSl_eq K h2 h7]
  have hD : K.D.x = (normW K)[7]'(by simp [normW]) := rfl
  have hE : K.E.x = (normW K)[8]'(by simp [normW]) := rfl
  constructor
  · rw [hD]; exact normW_ne hL _ _ (by omega_arith)
  · rw [hE]; exact normW_ne hL _ _ (by omega_arith)

theorem DE_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) : K.D.x ≠ K.E.x := by
  have hD : K.D.x = (normW K)[7]'(by simp [normW]) := rfl
  have hE : K.E.x = (normW K)[8]'(by simp [normW]) := rfl
  rw [hD, hE]; exact normW_ne hL _ _ (by decide)

/-- A slot written but the table's is not a table slot. -/
theorem other_ne_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat} (hx : x ∈ winOther K)
    {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) {y : Nat} (hy : y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z]) :
    x ≠ y := by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 y hy
  exact hL.tbl_ne (List.mem_append_right _ hx) hi

/-- The table's slots of different coordinates or entries are distinct. -/
theorem tbl_coord_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) {m m' : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8)
    (h1' : 1 ≤ m') (h8' : m' ≤ 8) {c c' : Nat} (hc : c < 3) (hc' : c' < 3) (h : m ≠ m' ∨ c ≠ c') :
    K.tbl + 8 * K.M.n * (3 * (m - 1) + c) ≠ K.tbl + 8 * K.M.n * (3 * (m' - 1) + c') :=
  hL.tbl_ne₂ (by omega_arith)

theorem tblPt_coords (K : WinCfg) (m : Nat) :
    (K.tblPt m).x = K.tbl + 8 * K.M.n * (3 * (m - 1) + 0) ∧
    (K.tblPt m).y = K.tbl + 8 * K.M.n * (3 * (m - 1) + 1) ∧
    (K.tblPt m).z = K.tbl + 8 * K.M.n * (3 * (m - 1) + 2) :=
  ⟨by rw [tblPt_x]; rfl, tblPt_y K m, tblPt_z K m⟩

theorem tmv_congr {C : Curve} {n : Nat} {base : Addr} {s t : State} {x : Nat}
    (h : wordsVal t.mem base x n = wordsVal s.mem base x n) : tmv C n base t x = tmv C n base s x := by
  show toM _ _ _ = toM _ _ _; rw [h]

/-! ## The prefix products -/

/-- The prefix products of `Z`: `c_1 = Z_1`, `c_{j+1} = c_j Z_{j+1}`. -/
def cprod {C : Curve} (Z : Nat → Fe C) : Nat → Fe C
  | 0 => Z 1
  | 1 => Z 1
  | j + 2 => cprod Z (j + 1) * Z (j + 2)

/-- The table's `Z` in a state. -/
abbrev tz (K : WinCfg) (C : Curve) (base : Addr) (s : State) (j : Nat) : Fe C :=
  tmv C K.M.n base s (K.tblPt j).z

/-- After the products `c_2 … c_{i+1}`, from `s₀`: they in their slots, and the
other slots as in `s₀`. -/
structure PreInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (i : Nat)
    (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) s₀ t
  unch : Unch base (winW K) s₀.mem t.mem
  mod : ModOkW K.M size C.p t.mem base
  lt : ∀ j, 2 ≤ j → j ≤ i + 1 → wordsVal t.mem base (WinCfg.prodSl K j) K.M.n < C.p
  val : ∀ j, 2 ≤ j → j ≤ i + 1 → tmv C K.M.n base t (WinCfg.prodSl K j) = cprod (tz K C base s₀) j
  same : ∀ x ∈ winSlots K, (∀ j, 2 ≤ j → j ≤ i + 1 → x ≠ WinCfg.prodSl K j) →
    wordsVal t.mem base x K.M.n = wordsVal s₀.mem base x K.M.n

theorem winW_append {K : WinCfg} : ∀ w ∈ winW K ++ winW K, w ∈ winW K := fun _ hw =>
  (List.mem_append.mp hw).elim id id

/-- A table `Z` keeps its number while only the prefix products are written. -/
theorem tz_same {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8)
    {i : Nat} : (K.tblPt m).z ∈ winSlots K ∧
      ∀ j, 2 ≤ j → j ≤ i → j ≤ 8 → (K.tblPt m).z ≠ WinCfg.prodSl K j :=
  ⟨(tblPt_slots K h1 h8 _ (by simp)).1, fun j h2 _ h8' h =>
    other_ne_tbl hL (prodSl_other h2 h8') h1 h8 (y := (K.tblPt m).z) (by simp) h.symm⟩

/-- `c_2 … c_8`, from the table's `Z`. -/
theorem prod_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {P : Point C} {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkW K.M size C.p s₀.mem base) (hT : TblOk K C base P 8 s₀) :
    WP isa (fprogB K.M (WinCfg.prodOps K)).inline s₀ (PreInv K C base size s₀ 7) := by
  rw [WinCfg.prodOps, List.map_eq_flatMap]
  have I₀ : PreInv K C base size s₀ 0 s₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, fun j h2 h1 => absurd h2 (by omega_arith),
      fun j h2 h1 => absurd h2 (by omega_arith), fun _ _ _ => rfl⟩
  refine fprogB_range_ok (N := 7) (fun i hi t I => ?_) 7 (Nat.le_refl _) s₀ I₀
  have hsa := tz_same hL (m := i + 2) (by omega_arith) (by omega_arith) (i := i + 1)
  have ltb : wordsVal t.mem base (K.tblPt (i + 2)).z K.M.n < C.p := by
    rw [I.same _ hsa.1 fun j h2 hj => hsa.2 j h2 hj (by omega_arith)]
    exact (hT (i + 2) (by omega_arith) (by omega_arith)).1 _ (by simp)
  have va : wordsVal t.mem base (WinCfg.prodSl K (i + 1)) K.M.n < C.p ∧
      tmv C K.M.n base t (WinCfg.prodSl K (i + 1)) = cprod (tz K C base s₀) (i + 1) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have h1 := tz_same hL (m := 1) (by omega_arith) (by omega_arith) (i := 1)
      have e := I.same _ h1.1 fun j h2 hj => h1.2 j h2 hj (by omega_arith)
      refine ⟨by rw [prodSl_one, e]; exact (hT 1 (by omega_arith) (by omega_arith)).1 _ (by simp), ?_⟩
      rw [prodSl_one, tmv_congr e]; rfl
    · exact ⟨I.lt _ (by omega_arith) (by omega_arith), I.val _ (by omega_arith) (by omega_arith)⟩
  have hoW : WinCfg.prodSl K (i + 2) ∈ winWs K := winOther_ws K _ (prodSl_other (by omega_arith) (by omega_arith))
  have haS : WinCfg.prodSl K (i + 1) ∈ winSlots K := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact (tz_same hL (m := 1) (by omega_arith) (by omega_arith) (i := 0)).1
    · exact winOther_mem (prodSl_other (by omega_arith) (by omega_arith))
  refine WP.mono (slotMul_ok hL hp I.scr I.mod hoW haS hsa.1 va.1 ltb)
    fun u ⟨su, ku, Uu, Mu, lu, vu, eu⟩ => ?_
  have ne : ∀ j, 2 ≤ j → j ≤ i + 1 → WinCfg.prodSl K j ≠ WinCfg.prodSl K (i + 2) := fun j h2 hj h =>
    absurd (prodSl_inj hL h2 (by omega_arith) (by omega_arith) (by omega_arith) h) (by omega_arith)
  refine ⟨su, I.keep.trans ku, (I.unch.trans Uu).mono winW_append, Mu, fun j h2 hj => ?_,
    fun j h2 hj => ?_, fun x hx hne => ?_⟩
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [eu _ (winOther_mem (prodSl_other h2 (by omega_arith))) (ne j h2 (by omega_arith))]
      exact I.lt j h2 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      exact lu
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [tmv_congr (eu _ (winOther_mem (prodSl_other h2 (by omega_arith))) (ne j h2 (by omega_arith)))]
      exact I.val j h2 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      rw [vu, va.2, tmv_congr (I.same _ hsa.1 fun j h2 hj => hsa.2 j h2 hj (by omega_arith))]
      rfl
  · rw [eu x hx (hne _ (by omega_arith) (by omega_arith))]
    exact I.same x hx fun j h2 hj => hne j h2 (by omega_arith)

/-! ## Back from entry `8` -/

section Coords
variable {K : WinCfg} {size : Nat} (hL : WinLay K size)
include hL

theorem txy {m m' : Nat} : (K.tblPt m).x ≠ (K.tblPt m').y := by
  rw [tblPt_x, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

theorem tyx {m m' : Nat} : (K.tblPt m).y ≠ (K.tblPt m').x := fun h => txy hL h.symm

theorem txx {m m' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (h : m ≠ m') : (K.tblPt m).x ≠ (K.tblPt m').x := by
  rw [tblPt_x, tblPt_x]; exact hL.tbl_ne₂ (by omega_arith)

theorem tyy {m m' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (h : m ≠ m') : (K.tblPt m).y ≠ (K.tblPt m').y := by
  rw [tblPt_y, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

theorem tzx {m m' : Nat} : (K.tblPt m).z ≠ (K.tblPt m').x := by
  rw [tblPt_z, tblPt_x]; exact hL.tbl_ne₂ (by omega_arith)

theorem tzy {m m' : Nat} : (K.tblPt m).z ≠ (K.tblPt m').y := by
  rw [tblPt_z, tblPt_y]; exact hL.tbl_ne₂ (by omega_arith)

/-- `D.x` and `E.x` are not table slots. -/
theorem DE_tbl {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], K.D.x ≠ y ∧ K.E.x ≠ y := fun y hy =>
  ⟨other_ne_tbl hL (by win_mem) h1 h8 hy, other_ne_tbl hL (by win_mem) h1 h8 hy⟩

/-- The slot of `c_j`, `j ≤ 7`: not `D.x`, `E.x` or a table `X` or `Y`. -/
theorem prodSl_ne {j : Nat} (h1 : 1 ≤ j) (h7 : j ≤ 7) {m : Nat} (hm1 : 1 ≤ m) (hm8 : m ≤ 8) :
    WinCfg.prodSl K j ≠ K.D.x ∧ WinCfg.prodSl K j ≠ K.E.x ∧
      WinCfg.prodSl K j ≠ (K.tblPt m).x ∧ WinCfg.prodSl K j ≠ (K.tblPt m).y := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega_arith
    rw [prodSl_one]
    have d := DE_tbl hL (m := 1) (Nat.le_refl _) (by omega_arith) (K.tblPt 1).z (by simp)
    exact ⟨Ne.symm d.1, Ne.symm d.2, tzx hL, tzy hL⟩
  · have o := prodSl_other (K := K) hj (by omega_arith)
    exact ⟨(prodSl_ne_DE hL hj (by omega_arith)).1, (prodSl_ne_DE hL hj (by omega_arith)).2,
      other_ne_tbl hL o hm1 hm8 (by simp), other_ne_tbl hL o hm1 hm8 (by simp)⟩

end Coords

theorem prodSl_slots {K : WinCfg} {j : Nat} (h1 : 1 ≤ j) (h8 : j ≤ 8) : WinCfg.prodSl K j ∈ winSlots K := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega_arith
    rw [prodSl_one]
    exact (tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_arith) (K.tblPt 1).z (by simp)).1
  · exact winOther_mem (prodSl_other hj h8)

theorem cprod_succ {C : Curve} (Z : Nat → Fe C) {m : Nat} (h : 2 ≤ m) :
    cprod Z m = cprod Z (m - 1) * Z m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega_arith⟩
  rfl

theorem cprod_ne_zero {C : Curve} (hC : Law C) {Z : Nat → Fe C} (hZ : ∀ j, 1 ≤ j → j ≤ 8 → Z j ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ 8 → cprod Z m ≠ 0
  | 0, h, _ => absurd h (by omega_arith)
  | 1, _, _ => hZ 1 (Nat.le_refl _) (by omega_arith)
  | j + 2, _, h8 => hC.mul_ne_zero (cprod_ne_zero hC hZ (j + 1) (by omega_arith) (by omega_arith)) (hZ _ (by omega_arith) h8)

/-- The table and the products as the inversion leaves them: `c_1 … c_7`, and
the entries' `X`, `Y`, `Z` (nonzero). -/
structure BackStart (K : WinCfg) (C : Curve) (base : Addr) (u₀ : State) (X Y Z : Nat → Fe C) : Prop where
  c : ∀ j, 1 ≤ j → j ≤ 7 → wordsVal u₀.mem base (WinCfg.prodSl K j) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (WinCfg.prodSl K j) = cprod Z j
  x : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).x K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).x = X j
  y : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).y K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).y = Y j
  z : ∀ j, 1 ≤ j → j ≤ 8 → wordsVal u₀.mem base (K.tblPt j).z K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.tblPt j).z = Z j
  nz : ∀ j, 1 ≤ j → j ≤ 8 → Z j ≠ 0

/-- After entries `8 … 9 - i`: `c_{8-i}^(p-2)` in `E.x`, those entries' `X`,
`Y` by their `Z^(p-2)`, and the other slots but `D.x` as at `u₀`. -/
structure BackInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (u₀ : State) (X Y Z : Nat → Fe C)
    (i : Nat) (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) u₀ t
  unch : Unch base (winW K) u₀.mem t.mem
  mod : ModOkW K.M size C.p t.mem base
  ex_lt : wordsVal t.mem base K.E.x K.M.n < C.p
  ex : tmv C K.M.n base t K.E.x = cprod Z (8 - i) ^ (C.p - 2)
  done : ∀ j, 8 - i < j → j ≤ 8 →
    wordsVal t.mem base (K.tblPt j).x K.M.n < C.p ∧ wordsVal t.mem base (K.tblPt j).y K.M.n < C.p ∧
    tmv C K.M.n base t (K.tblPt j).x = X j * Z j ^ (C.p - 2) ∧
    tmv C K.M.n base t (K.tblPt j).y = Y j * Z j ^ (C.p - 2)
  same : ∀ x ∈ winSlots K, x ≠ K.D.x → x ≠ K.E.x →
    (∀ j, 8 - i < j → j ≤ 8 → x ≠ (K.tblPt j).x ∧ x ≠ (K.tblPt j).y) →
    wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n

/-- Entry `m = 8 - i` (`2 ≤ m`). -/
theorem back_step {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {u₀ : State} {X Y Z : Nat → Fe C}
    (B : BackStart K C base u₀ X Y Z) {i : Nat} (hi : i < 7) {t : State}
    (I : BackInv K C base size u₀ X Y Z i t) :
    WP isa (fprogB K.M (WinCfg.backOps K (8 - i))).inline t (BackInv K C base size u₀ X Y Z (i + 1)) := by
  generalize hm : 8 - i = m
  have hm2 : 2 ≤ m := by omega_arith
  have hm8 : m ≤ 8 := by omega_arith
  have hmi : 8 - (i + 1) = m - 1 := by omega_arith
  have dDE := DE_ne hL
  have tm := DE_tbl hL (m := m) (by omega_arith) hm8
  have pc := prodSl_ne hL (j := m - 1) (by omega_arith) (by omega_arith) (m := m) (by omega_arith) hm8
  have Dw : K.D.x ∈ winWs K := winOther_ws K _ (by win_mem)
  have Ew : K.E.x ∈ winWs K := winOther_ws K _ (by win_mem)
  have st := tblPt_slots K (m := m) (by omega_arith) hm8
  have xw := (st _ (by simp : (K.tblPt m).x ∈ _)).2
  have yw := (st _ (by simp : (K.tblPt m).y ∈ _)).2
  have zS := (st _ (by simp : (K.tblPt m).z ∈ _)).1
  -- What is not done at `t`.
  have nd : ∀ {x}, x ∈ winSlots K → x ≠ K.D.x → x ≠ K.E.x → (∀ j, m < j → j ≤ 8 →
      x ≠ (K.tblPt j).x ∧ x ≠ (K.tblPt j).y) → wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n :=
    fun hx h1 h2 h3 => I.same _ hx h1 h2 fun j hj hj' => h3 j (by omega_arith) hj'
  have cS := prodSl_slots (K := K) (j := m - 1) (by omega_arith) (by omega_arith)
  have ec : wordsVal t.mem base (WinCfg.prodSl K (m - 1)) K.M.n =
      wordsVal u₀.mem base (WinCfg.prodSl K (m - 1)) K.M.n :=
    nd cS pc.1 pc.2.1 fun j hj hj' => (prodSl_ne hL (j := m - 1) (by omega_arith) (by omega_arith) (m := j) (by omega_arith) hj').2.2
  have ez : wordsVal t.mem base (K.tblPt m).z K.M.n = wordsVal u₀.mem base (K.tblPt m).z K.M.n :=
    nd zS (tm _ (by simp)).1.symm (tm _ (by simp)).2.symm fun j _ _ => ⟨tzx hL, tzy hL⟩
  have ex0 : wordsVal t.mem base (K.tblPt m).x K.M.n = wordsVal u₀.mem base (K.tblPt m).x K.M.n :=
    nd (winWs_slots K _ xw) (tm _ (by simp)).1.symm (tm _ (by simp)).2.symm fun j hj _ =>
      ⟨txx hL (by omega_arith) (by omega_arith) (by omega_arith), txy hL⟩
  have ey0 : wordsVal t.mem base (K.tblPt m).y K.M.n = wordsVal u₀.mem base (K.tblPt m).y K.M.n :=
    nd (winWs_slots K _ yw) (tm _ (by simp)).1.symm (tm _ (by simp)).2.symm fun j hj _ =>
      ⟨tyx hL, tyy hL (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hcm := cprod_succ Z hm2
  have nz := cprod_ne_zero hC B.nz (m - 1) (by omega_arith) (by omega_arith)
  obtain ⟨tr1, tr2⟩ := trick_step hC nz (B.nz m (by omega_arith) hm8)
  rw [← hcm] at tr1 tr2
  rw [WinCfg.backOps, fprogB_cons_iff]
  -- `D.x = E.x c_{m-1}`.
  refine WP.mono (slotMul_ok hL hp I.scr I.mod Dw (winWs_slots K _ Ew) cS I.ex_lt
    (by rw [ec]; exact (B.c _ (by omega_arith) (by omega_arith)).1)) fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  rw [fprogB_cons_iff]
  have ex₁ := e₁ _ (winWs_slots K _ Ew) (Ne.symm dDE)
  -- `E.x = E.x Z_m`.
  refine WP.mono (slotMul_ok hL hp s₁ M₁ Ew (winWs_slots K _ Ew) zS (by rw [ex₁]; exact I.ex_lt)
    (by rw [e₁ _ zS (tm _ (by simp)).1.symm, ez]; exact (B.z m (by omega_arith) hm8).1))
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  rw [fprogB_cons_iff]
  have dx₂ := e₂ _ (winWs_slots K _ Dw) dDE
  have xx₂ : wordsVal t₂.mem base (K.tblPt m).x K.M.n = wordsVal u₀.mem base (K.tblPt m).x K.M.n := by
    rw [e₂ _ (winWs_slots K _ xw) (tm _ (by simp)).2.symm, e₁ _ (winWs_slots K _ xw) (tm _ (by simp)).1.symm, ex0]
  -- `X_m = X_m D.x`.
  refine WP.mono (slotMul_ok hL hp s₂ M₂ xw (winWs_slots K _ xw) (winWs_slots K _ Dw)
    (by rw [xx₂]; exact (B.x m (by omega_arith) hm8).1) (by rw [dx₂]; exact l₁))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_
  have dx₃ := e₃ _ (winWs_slots K _ Dw) (tm _ (by simp)).1
  have yy₃ : wordsVal t₃.mem base (K.tblPt m).y K.M.n = wordsVal u₀.mem base (K.tblPt m).y K.M.n := by
    rw [e₃ _ (winWs_slots K _ yw) (tyx hL), e₂ _ (winWs_slots K _ yw) (tm _ (by simp)).2.symm,
      e₁ _ (winWs_slots K _ yw) (tm _ (by simp)).1.symm, ey0]
  -- `Y_m = Y_m D.x`.
  refine WP.mono (slotMul_ok hL hp s₃ M₃ yw (winWs_slots K _ yw) (winWs_slots K _ Dw)
    (by rw [yy₃]; exact (B.y m (by omega_arith) hm8).1) (by rw [dx₃, dx₂]; exact l₁))
    fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  -- Every slot but the four written keeps its number.
  have keep4 : ∀ x ∈ winSlots K, x ≠ K.D.x → x ≠ K.E.x → x ≠ (K.tblPt m).x → x ≠ (K.tblPt m).y →
      wordsVal t₄.mem base x K.M.n = wordsVal t.mem base x K.M.n := fun x hx h1 h2 h3 h4 => by
    rw [e₄ x hx h4, e₃ x hx h3, e₂ x hx h2, e₁ x hx h1]
  have vD : tmv C K.M.n base t₁ K.D.x = Z m ^ (C.p - 2) := by
    rw [v₁, I.ex, hm, tmv_congr ec, (B.c _ (by omega_arith) (by omega_arith)).2]; exact tr1
  have vE : tmv C K.M.n base t₂ K.E.x = cprod Z (m - 1) ^ (C.p - 2) := by
    rw [v₂, tmv_congr ex₁, I.ex, hm, tmv_congr (e₁ _ zS (tm _ (by simp)).1.symm), tmv_congr ez,
      (B.z m (by omega_arith) hm8).2]; exact tr2
  have ex₄ : wordsVal t₄.mem base K.E.x K.M.n = wordsVal t₂.mem base K.E.x K.M.n := by
    rw [e₄ _ (winWs_slots K _ Ew) (tm _ (by simp)).2, e₃ _ (winWs_slots K _ Ew) (tm _ (by simp)).2]
  have xx₄ : wordsVal t₄.mem base (K.tblPt m).x K.M.n = wordsVal t₃.mem base (K.tblPt m).x K.M.n :=
    e₄ _ (winWs_slots K _ xw) (txy hL)
  refine ⟨s₄, I.keep.trans (k₁.trans (k₂.trans (k₃.trans k₄))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans U₄)))).mono fun w hw => ?_, M₄,
    by rw [ex₄]; exact l₂, by rw [hmi, tmv_congr ex₄, vE], fun j hj hj8 => ?_, fun x hx h1 h2 h3 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge m j with hj' | hj'
    · obtain ⟨a1, a2, a3, a4⟩ := I.done j (by omega_arith) hj8
      have tj := DE_tbl hL (m := j) (by omega_arith) hj8
      have ex : wordsVal t₄.mem base (K.tblPt j).x K.M.n = wordsVal t.mem base (K.tblPt j).x K.M.n :=
        keep4 _ (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp)).1 (tj _ (by simp)).1.symm
          (tj _ (by simp)).2.symm (txx hL (by omega_arith) (by omega_arith) (by omega_arith)) (txy hL)
      have ey : wordsVal t₄.mem base (K.tblPt j).y K.M.n = wordsVal t.mem base (K.tblPt j).y K.M.n :=
        keep4 _ (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp)).1 (tj _ (by simp)).1.symm
          (tj _ (by simp)).2.symm (tyx hL) (tyy hL (by omega_arith) (by omega_arith) (by omega_arith))
      exact ⟨by rw [ex]; exact a1, by rw [ey]; exact a2, by rw [tmv_congr ex]; exact a3,
        by rw [tmv_congr ey]; exact a4⟩
    · obtain rfl : j = m := by omega_arith
      refine ⟨by rw [xx₄]; exact l₃, l₄, ?_, ?_⟩
      · rw [tmv_congr xx₄, v₃, tmv_congr xx₂, (B.x j (by omega_arith) hj8).2, tmv_congr dx₂, vD]
      · rw [v₄, tmv_congr yy₃, (B.y j (by omega_arith) hj8).2, tmv_congr dx₃, tmv_congr dx₂, vD]
  · have hm' := h3 m (by omega_arith) hm8
    rw [keep4 x hx h1 h2 hm'.1 hm'.2]
    exact I.same x hx h1 h2 fun j hj hj' => h3 j (by omega_arith) hj'

theorem fprog_flatMap (M : Mod) (l : List Nat) (g : Nat → List FOp) :
    fprog M (l.flatMap g) = l.flatMap fun i => fprog M (g i) := by
  simp only [fprog, List.flatMap_assoc]

/-- The entries' `X` and `Y` by their `Z^(p-2)`, from `c_8^(p-2)` in `E.x`. -/
theorem back_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {u₀ : State} {X Y Z : Nat → Fe C}
    (B : BackStart K C base u₀ X Y Z) (hs : Scr u₀ base size) (hM : ModOkW K.M size C.p u₀.mem base)
    (hel : wordsVal u₀.mem base K.E.x K.M.n < C.p)
    (hev : tmv C K.M.n base u₀ K.E.x = cprod Z 8 ^ (C.p - 2)) :
    WP isa (fprogB K.M (WinCfg.normOps K)).inline u₀ fun t => Scr t base size ∧
      KeepRegs (clob K.M.n) u₀ t ∧ Unch base (winW K) u₀.mem t.mem ∧ ModOkW K.M size C.p t.mem base ∧
      ∀ j, 1 ≤ j → j ≤ 8 →
        wordsVal t.mem base (K.tblPt j).x K.M.n < C.p ∧ wordsVal t.mem base (K.tblPt j).y K.M.n < C.p ∧
        tmv C K.M.n base t (K.tblPt j).x = X j * Z j ^ (C.p - 2) ∧
        tmv C K.M.n base t (K.tblPt j).y = Y j * Z j ^ (C.p - 2) := by
  rw [WinCfg.normOps, fprogB_append_iff]
  have I₀ : BackInv K C base size u₀ X Y Z 0 u₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, hel, hev, fun j hj hj' => absurd hj' (by omega_arith),
      fun _ _ _ _ _ => rfl⟩
  refine WP.mono (fprogB_range_ok (N := 7) (fun i hi t I => back_step hL hp hC B hi I) 7 (Nat.le_refl _) u₀ I₀)
    fun t I => ?_
  have Ew : K.E.x ∈ winWs K := winOther_ws K _ (by win_mem)
  have st := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_arith)
  have xw := (st _ (by simp : (K.tblPt 1).x ∈ _)).2
  have yw := (st _ (by simp : (K.tblPt 1).y ∈ _)).2
  have t1 := DE_tbl hL (m := 1) (Nat.le_refl _) (by omega_arith)
  have ex1 : wordsVal t.mem base (K.tblPt 1).x K.M.n = wordsVal u₀.mem base (K.tblPt 1).x K.M.n :=
    I.same _ (winWs_slots K _ xw) (t1 _ (by simp)).1.symm (t1 _ (by simp)).2.symm fun j hj _ =>
      ⟨txx hL (by omega_arith) (by omega_arith) (by omega_arith), txy hL⟩
  have ey1 : wordsVal t.mem base (K.tblPt 1).y K.M.n = wordsVal u₀.mem base (K.tblPt 1).y K.M.n :=
    I.same _ (winWs_slots K _ yw) (t1 _ (by simp)).1.symm (t1 _ (by simp)).2.symm fun j hj _ =>
      ⟨tyx hL, tyy hL (by omega_arith) (by omega_arith) (by omega_arith)⟩
  rw [fprogB_cons_iff]
  refine WP.mono (slotMul_ok hL hp I.scr I.mod xw (winWs_slots K _ xw) (winWs_slots K _ Ew)
    (by rw [ex1]; exact (B.x 1 (Nat.le_refl _) (by omega_arith)).1) I.ex_lt)
    fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  have ee₁ := e₁ _ (winWs_slots K _ Ew) (t1 _ (by simp)).2
  refine WP.mono (slotMul_ok hL hp s₁ M₁ yw (winWs_slots K _ yw) (winWs_slots K _ Ew)
    (by rw [e₁ _ (winWs_slots K _ yw) (tyx hL), ey1]; exact (B.y 1 (Nat.le_refl _) (by omega_arith)).1)
    (by rw [ee₁]; exact I.ex_lt)) fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  refine ⟨s₂, I.keep.trans (k₁.trans k₂), (I.unch.trans (U₁.trans U₂)).mono fun w hw => ?_, M₂,
    fun j hj hj8 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge 1 j with hj' | hj'
    · obtain ⟨a1, a2, a3, a4⟩ := I.done j (by omega_arith) hj8
      have ex : wordsVal t₂.mem base (K.tblPt j).x K.M.n = wordsVal t.mem base (K.tblPt j).x K.M.n := by
        have h := (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp : (K.tblPt j).x ∈ _)).1
        rw [e₂ _ h (txy hL), e₁ _ h (txx hL (by omega_arith) (by omega_arith) (by omega_arith))]
      have ey : wordsVal t₂.mem base (K.tblPt j).y K.M.n = wordsVal t.mem base (K.tblPt j).y K.M.n := by
        have h := (tblPt_slots K (m := j) (by omega_arith) hj8 _ (by simp : (K.tblPt j).y ∈ _)).1
        rw [e₂ _ h (tyy hL (by omega_arith) (by omega_arith) (by omega_arith)), e₁ _ h (tyx hL)]
      exact ⟨by rw [ex]; exact a1, by rw [ey]; exact a2, by rw [tmv_congr ex]; exact a3,
        by rw [tmv_congr ey]; exact a4⟩
    · obtain rfl : j = 1 := by omega_arith
      have xx₂ := e₂ _ (winWs_slots K _ xw) (txy hL)
      refine ⟨by rw [xx₂]; exact l₁, l₂, ?_, ?_⟩
      · rw [tmv_congr xx₂, v₁, tmv_congr ex1, (B.x 1 (Nat.le_refl _) (by omega_arith)).2, I.ex]; rfl
      · rw [v₂, tmv_congr (e₁ _ (winWs_slots K _ yw) (tyx hL)), tmv_congr ey1,
          (B.y 1 (Nat.le_refl _) (by omega_arith)).2, tmv_congr ee₁, I.ex]; rfl

/-! ## Every `Z` one, and the table -/

/-- The entries' `Z` set to one: those of `1 … i`. -/
theorem ones_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {x : Nat}
    (hx : x < 2 ^ (64 * K.M.n)) :
    ∀ i ≤ 8, ∀ s : State, Scr s base size →
      WP isa (.block ((List.range i).flatMap fun j => setConst K.M.n (K.tblPt (j + 1)).z x)) s fun t =>
        Scr t base size ∧ KeepRegs [.rax] s t ∧ Unch base (winW K) s.mem t.mem ∧
        (∀ j, 1 ≤ j → j ≤ i → wordsVal t.mem base (K.tblPt j).z K.M.n = x) ∧
        ∀ y ∈ winSlots K, (∀ j, 1 ≤ j → j ≤ i → y ≠ (K.tblPt j).z) →
          wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n := by
  intro i hi s hs
  refine block_range_ok (N := 8) (Inv := fun i t => Scr t base size ∧ KeepRegs [.rax] s t ∧
      Unch base (winW K) s.mem t.mem ∧ (∀ j, 1 ≤ j → j ≤ i → wordsVal t.mem base (K.tblPt j).z K.M.n = x) ∧
      ∀ y ∈ winSlots K, (∀ j, 1 ≤ j → j ≤ i → y ≠ (K.tblPt j).z) →
        wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n)
    (fun i hi t ⟨st, kt, Ut, vt, et⟩ => ?_) i hi s
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, fun j h1 h0 => absurd h1 (by omega_arith), fun _ _ _ => rfl⟩
  have zs := tblPt_slots K (m := i + 1) (by omega_arith) (by omega_arith) _ (by simp : (K.tblPt (i + 1)).z ∈ _)
  refine WP.mono (setConst_ok st (n := K.M.n) (o := (K.tblPt (i + 1)).z) (hL.lay.le _ zs.1) hx)
    fun u ⟨eu, ku, Ou⟩ => ?_
  have hn := st.nowrap
  have same : ∀ y ∈ winSlots K, y ≠ (K.tblPt (i + 1)).z →
      wordsVal u.mem base y K.M.n = wordsVal t.mem base y K.M.n := fun y hy hne =>
    Ou.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact hL.lay.apart y _ hy zs.1 hne) (by have := hL.lay.le y hy; omega_arith)
  refine ⟨st.of_keepRegs ku (by decide), kt.trans ku, (Ut.trans Ou.unch).mono fun w hw => ?_,
    fun j h1 hj => ?_, fun y hy hne => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · rw [List.mem_singleton.mp hw]
      simp only [winW, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, zs.2, rfl⟩
  · rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
    · rw [same _ (tblPt_slots K (m := j) h1 (by omega_arith) _ (by simp : (K.tblPt j).z ∈ _)).1
        (fun h => by rw [tblPt_z, tblPt_z] at h; exact hL.tbl_ne₂ (by omega_arith) h)]
      exact vt j h1 (by omega_arith)
    · obtain rfl : j = i + 1 := by omega_arith
      exact eu
  · rw [same y hy (hne _ (by omega_arith) (Nat.le_refl _))]
    exact et y hy fun j h1 hj => hne j h1 (by omega_arith)

theorem rdi_not_invClob' (n : Nat) : Reg.rdi ∉ invClob n := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact absurd h (by decide)
  rcases List.mem_cons.mp h with h | h
  · exact absurd h (by decide)
  · exact rdi_not_clob n h

/-- What the inversion `inv` does: `E.x = R.z^(p-2)`, writing `IW`: `E.x`, the
temporary area, and areas apart from the modulus and the window's slots. -/
structure InvSpecW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (inv : Prog isa)
    (IW : List (Nat × Nat)) : Prop where
  ok : ∀ t : State, Scr t base size → ModOkW K.M size C.p t.mem base →
    wordsVal t.mem base K.R.z K.M.n < C.p → WP isa inv.inline t fun t' =>
      KeepRegs (invClob K.M.n) t t' ∧ Unch base IW t.mem t'.mem ∧
      wordsVal t'.mem base K.E.x K.M.n < C.p ∧
      tmv C K.M.n base t' K.E.x = tmv C K.M.n base t K.R.z ^ (C.p - 2)
  w : ∀ w ∈ IW, w = (K.E.x, 8 * K.M.n) ∨ w = (K.M.tmp, 8 * K.M.n) ∨
    ((K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo) ∧
      ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
  bits : ∀ w ∈ IW, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

theorem InvSpecW.same {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {inv : Prog isa}
    {IW : List (Nat × Nat)} (h : InvSpecW K C base size inv IW) (hL : WinLay K size) {m m' : Mem}
    (hU : Unch base IW m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat} (hx : x ∈ winSlots K)
    (hne : x ≠ K.E.x) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (fun w hw => by
    rcases h.w w hw with rfl | rfl | ⟨-, h⟩
    · exact hL.lay.apart x _ hx (winOther_mem (by win_mem)) hne
    · exact hL.lay.tmp x hx
    · exact h x hx) (by have := hL.lay.le x hx; omega_arith)

theorem InvSpecW.mo {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {inv : Prog isa}
    {IW : List (Nat × Nat)} (h : InvSpecW K C base size inv IW) (hL : WinLay K size) {mem : Mem}
    (hM : ModOkW K.M size C.p mem base) : ∀ w ∈ IW, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  rcases h.w w hw with rfl | rfl | ⟨h, -⟩
  · have := hL.lay.mo K.E.x (winOther_mem (by win_mem)); dsimp only; omega_arith
  · have := hM.sep; dsimp only; omega_arith
  · exact h

/-- The table into affine coordinates, for entries other than `O`. -/
theorem normTbl_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity) {inv : Prog isa} {IW : List (Nat × Nat)}
    (hI : InvSpecW K C base size inv IW) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hT : TblOk K C base P 8 s) :
    WP isa (WinCfg.normTbl K inv).inline s fun s' => Scr s' base size ∧ KeepRegs (invClob K.M.n) s s' ∧
      Unch base (winW K ++ IW) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      TblOkR K C base (RepA C) P 8 s' := by
  have hn := hs.nowrap
  rw [WinCfg.normTbl]
  refine WP.seq (WP.mono (prod_ok hL hp hs hM hT) fun t₇ I₇ => ?_)
  refine WP.seq (WP.mono (hI.ok t₇ I₇.scr I₇.mod (I₇.lt 8 (by omega_arith) (by omega_arith)))
    fun u₀ ⟨Ku, Uu, lu, vu⟩ => ?_)
  have hsu := I₇.scr.of_keepRegs Ku (rdi_not_invClob' _)
  have Mu := I₇.mod.unch Uu (hI.mo hL I₇.mod) hn
  -- The table and the products at `u₀`.
  have tsame : ∀ {m}, 1 ≤ m → m ≤ 8 → ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      wordsVal u₀.mem base y K.M.n = wordsVal s.mem base y K.M.n := fun h1 h8 y hy => by
    have ys := (tblPt_slots K h1 h8 y hy).1
    rw [hI.same hL Uu hn ys (DE_tbl hL h1 h8 y hy).2.symm]
    exact I₇.same y ys fun j h2 hj => (other_ne_tbl hL (prodSl_other h2 (by omega_arith)) h1 h8 hy).symm
  have B : BackStart K C base u₀ (fun j => tmv C K.M.n base s (K.tblPt j).x)
      (fun j => tmv C K.M.n base s (K.tblPt j).y) (tz K C base s) := by
    refine ⟨fun j h1 h7 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_, fun j h1 h8 => ?_⟩
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · obtain rfl : j = 1 := by omega_arith
        have e := tsame (m := 1) (Nat.le_refl _) (by omega_arith) (K.tblPt 1).z (by simp)
        rw [prodSl_one, e, tmv_congr e]
        exact ⟨(hT 1 (Nat.le_refl _) (by omega_arith)).1 _ (by simp), rfl⟩
      · have e := hI.same hL Uu hn (winOther_mem (prodSl_other hj (by omega_arith))) (prodSl_ne_DE hL hj (by omega_arith)).2
        rw [e, tmv_congr e]
        exact ⟨I₇.lt j hj (by omega_arith), I₇.val j hj (by omega_arith)⟩
    · have e := tsame h1 h8 (K.tblPt j).x (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · have e := tsame h1 h8 (K.tblPt j).y (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · have e := tsame h1 h8 (K.tblPt j).z (by simp)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h8).1 _ (by simp), rfl⟩
    · exact fun h0 => hne j h1 h8 (((hT j h1 h8).2.z_eq_zero_iff).mp h0)
  refine WP.seq (WP.mono (back_ok hL hp hC B hsu Mu lu (by rw [vu]; exact congrArg (· ^ (C.p - 2)) (I₇.val 8 (by omega_arith) (Nat.le_refl _))))
    fun v ⟨sv, kv, Uv, Mv, dv⟩ => ?_)
  refine WP.mono (ones_ok hL (x := K.one) (Nat.lt_trans hone_lt hpn) 8 (Nat.le_refl _) v sv)
    fun w ⟨sw, kw, Uw, ow, ew⟩ => ?_
  have c1 : ∀ r ∈ [Reg.rax], r ∈ invClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [invClob, powClob, clob]
  have c2 : ∀ r ∈ clob K.M.n, r ∈ invClob K.M.n := fun r h =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have U : Unch base (winW K ++ IW) s.mem w.mem :=
    (I₇.unch.trans (Uu.trans (Uv.trans Uw))).mono fun x hx => by
      simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx | hx | hx <;> simp [hx]
  refine ⟨sw, ((I₇.keep.mono c2).trans Ku).trans ((kv.mono c2).trans (kw.mono c1)), U,
    Mv.unch Uw (fun x hx => winW_mo hL Mv x hx) hn, fun j h1 h8 => ?_⟩
  obtain ⟨l1, l2, v1, v2⟩ := dv j h1 h8
  have zs := tblPt_slots K (m := j) h1 h8
  have ex : wordsVal w.mem base (K.tblPt j).x K.M.n = wordsVal v.mem base (K.tblPt j).x K.M.n :=
    ew _ (zs _ (by simp)).1 fun j' _ _ h => tzx hL h.symm
  have ey : wordsVal w.mem base (K.tblPt j).y K.M.n = wordsVal v.mem base (K.tblPt j).y K.M.n :=
    ew _ (zs _ (by simp)).1 fun j' _ _ h => tzy hL h.symm
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact l1
    · rw [ey]; exact l2
    · rw [ow j h1 h8]; exact hone_lt
  · have hz : tmv C K.M.n base w (K.tblPt j).z = 1 := by
      show toM _ _ _ = 1; rw [ow j h1 h8]; exact hone
    rw [tmv_congr ex, tmv_congr ey, v1, v2, hz]
    exact RepA.of_rep hC (hT j h1 h8).2 (hne j h1 h8)

end VG.Proof.Weierstrass.X86_64
