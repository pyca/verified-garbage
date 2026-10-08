import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
import VerifiedGarbage.Proof.Weierstrass.JacCoZ

/-!
# The Jacobian window method on x86-64: the table into affine coordinates

`JacWinCfg.normA` (Montgomery's trick) on the table `build` leaves
(`JTblOk`): the prefix products `c_m = Z_1 ⋯ Z_m` (`prodJ_ok`), `c_16^(p-2)` by
the inversion, then back from entry `16` (`backJ_ok`): `Z_m^(p-2) = c_m^(p-2)
c_{m-1}` and `c_{m-1}^(p-2) = c_m^(p-2) Z_m` (`trick_step`), each entry's `X`
and `Y` by the square and the cube of its `Z^(p-2)`, and every entry's `Z`,
`Z²` and `Z³` set to one (`onesJ_ok`): a table of Jacobian triples whose `Z`
is one (`normA_ok`). Each product is `slotMulJ_ok`, on the window's slots.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- One product on the window's slots, writing a slot written: the other
slots keep their numbers. -/
theorem slotMulJ_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) {o a b : Nat}
    (ho : o ∈ jwWs K) (ha : a ∈ jwSlots K) (hb : b ∈ jwSlots K) (hla : wordsVal s.mem base a K.M.n < C.p)
    (hlb : wordsVal s.mem base b K.M.n < C.p) :
    WP isa (.block (opCode K.M (.mul o a b))) s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (jwW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ jwSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  have I : Inv K.M base size C.p (· ∈ jwSlots K) [a, b] (tmv C K.M.n base s) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hla
      · exact hlb
  have hSo : o ∈ jwSlots K := ws_mem ho
  refine WP.mono (fop_ok hL.lay hp I (op := .mul o a b) (fun x hx => by
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hSo
      · exact ha
      · exact hb)
    (fun x hx => hx)) fun s' ⟨k, I'⟩ => ?_
  have U : Unch base [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem :=
    fun x hx => k.mem x (hx _ (List.mem_cons_self ..)) (hx (K.M.tmp, 8 * K.M.n) (by simp))
  refine ⟨I'.scr, ⟨k.gpr, k.rd, k.wr⟩, U.mono fun w hw => ?_, I'.mod, I'.lt o (List.mem_cons_self ..),
    ?_, fun x hx hxo => U.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; have := hs.nowrap; omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact mem_jwW_ws ho
    · exact mem_jwW_tmp
  · have v := I'.val o (List.mem_cons_self ..)
    simp only [FOp.run, Function.update_self] at v
    exact v
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hL.lay.apart x o hx hSo hxo
    · exact hL.lay.tmp x hx

theorem jwW_append : ∀ w ∈ jwW K ++ jwW K, w ∈ jwW K := fun _ hw =>
  (List.mem_append.mp hw).elim id id

/-! ## The slots -/

/-- Grid slots of distinct indices are distinct. -/
theorem jg_inj (hL : JacWinLay K size) {i j : Nat} (h : i ≠ j) : jg K i ≠ jg K j := by
  have := hL.n0
  rcases jg_apart K h with h | h <;> omega

theorem ent_eq (K : JacWinCfg) (m c : Nat) : K.ent m c = jg K (5 * (m - 1) + c) := rfl

/-- The index in the grid of `c_m`'s slot, `m < 16`. -/
def preG (m : Nat) : Nat := if m = 1 then 2 else 5 * (m - 1) + 3

theorem pre_eq (K : JacWinCfg) {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) : K.pre m = jg K (preG m) := by
  unfold JacWinCfg.pre preG
  by_cases h : m = 1
  · subst h; rfl
  · simp only [h, show ¬ m = 16 by omega, ↓reduceIte]; rfl

theorem pre_16 (K : JacWinCfg) : K.pre 16 = K.R.z := rfl

theorem preG_lt {m : Nat} (h15 : m ≤ 15) : preG m < 80 := by unfold preG; split <;> omega

section Slots
variable (hL : JacWinLay K size)
include hL

omit hL in
theorem RzD : K.R.z ∈ jwOther K ∧ K.D.x ∈ jwOther K ∧ K.D.y ∈ jwOther K ∧ K.D.z ∈ jwOther K := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> jw_mem

omit hL in
theorem pre_slots {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) : K.pre m ∈ jwSlots K := by
  rcases Nat.lt_or_ge m 16 with h | h
  · rw [pre_eq K h1 (by omega)]; exact jg_mem (by have := preG_lt (m := m) (by omega); omega)
  · obtain rfl : m = 16 := by omega
    exact other_mem (RzD (K := K)).1

omit hL in
theorem pre_ws {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) : K.pre m ∈ jwWs K := by
  rcases Nat.lt_or_ge m 16 with h | h
  · rw [pre_eq K h1 (by omega)]; exact jg_ws (by have := preG_lt (m := m) (by omega); omega)
  · obtain rfl : m = 16 := by omega
    exact other_ws (RzD (K := K)).1

theorem pre_inj {m m' : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (h1' : 1 ≤ m') (h16' : m' ≤ 16)
    (h : K.pre m = K.pre m') : m = m' := by
  refine Classical.byContradiction fun hne => ?_
  have g : ∀ {m}, 1 ≤ m → m ≤ 15 → K.R.z ≠ K.pre m := fun h1 h15 => by
    rw [pre_eq K h1 h15]
    exact hL.jg_ne (List.mem_append_right _ (RzD (K := K)).1) (by have := preG_lt (m := _) h15; omega)
  rcases Nat.lt_or_ge m 16 with hm | hm <;> rcases Nat.lt_or_ge m' 16 with hm' | hm'
  · rw [pre_eq K h1 (by omega), pre_eq K h1' (by omega)] at h
    refine jg_inj hL ?_ h
    unfold preG; split <;> split <;> omega
  · obtain rfl : m' = 16 := by omega
    exact g h1 (by omega) (h.trans (pre_16 K)).symm
  · obtain rfl : m = 16 := by omega
    exact g h1' (by omega) ((pre_16 K).symm.trans h)
  · exact hne (by omega)

/-- `c_m`'s slot is not `D`'s or `E.x`. -/
theorem pre_ne_DE {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) :
    K.pre m ≠ K.D.x ∧ K.pre m ≠ K.D.y ∧ K.pre m ≠ K.D.z ∧ K.pre m ≠ K.E.x := by
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  rcases Nat.lt_or_ge m 16 with hm | hm
  · rw [pre_eq K h1 (by omega)]
    have hg := preG_lt (m := m) (by omega)
    obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
    refine ⟨fun e => hL.jg_ne (List.mem_append_right _ dx) (by omega) e.symm,
      fun e => hL.jg_ne (List.mem_append_right _ dy) (by omega) e.symm,
      fun e => hL.jg_ne (List.mem_append_right _ dz) (by omega) e.symm, ?_⟩
    rw [hL.Tx]; exact jg_inj hL (by omega)
  · obtain rfl : m = 16 := by omega
    rw [pre_16]
    refine ⟨o 2 3 (by decide) (by decide) (by decide), o 2 4 (by decide) (by decide) (by decide),
      o 2 5 (by decide) (by decide) (by decide), ?_⟩
    rw [hL.Tx]; exact hL.jg_ne (List.mem_append_right _ (RzD (K := K)).1) (by decide)

/-- `c_m`'s slot is not an entry's `X` or `Y`, nor, for `m ≥ 2`, its `Z`. -/
theorem pre_ne_ent {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) {m' : Nat} (h1' : 1 ≤ m') (h16' : m' ≤ 16) :
    K.pre m ≠ K.ent m' 0 ∧ K.pre m ≠ K.ent m' 1 ∧ (2 ≤ m → K.pre m ≠ K.ent m' 2) := by
  rcases Nat.lt_or_ge m 16 with hm | hm
  · rw [pre_eq K h1 (by omega), ent_eq, ent_eq, ent_eq]
    refine ⟨jg_inj hL ?_, jg_inj hL ?_, fun h2 => jg_inj hL ?_⟩ <;> unfold preG <;> split <;> omega
  · obtain rfl : m = 16 := by omega
    rw [pre_16, ent_eq, ent_eq, ent_eq]
    have r := List.mem_append_right (jwRo K) (RzD (K := K)).1
    exact ⟨hL.jg_ne r (by omega), hL.jg_ne r (by omega), fun _ => hL.jg_ne r (by omega)⟩

/-- `D`'s slots and `E.x` are not entries' slots. -/
theorem DE_ent {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) :
    K.D.x ≠ K.ent m c ∧ K.D.y ≠ K.ent m c ∧ K.D.z ≠ K.ent m c ∧ K.E.x ≠ K.ent m c := by
  obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
  rw [ent_eq]
  refine ⟨hL.jg_ne (List.mem_append_right _ dx) (by omega), hL.jg_ne (List.mem_append_right _ dy) (by omega),
    hL.jg_ne (List.mem_append_right _ dz) (by omega), ?_⟩
  rw [hL.Tx]; exact jg_inj hL (by omega)

theorem ent_ne {m m' c c' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (hc : c < 5) (hc' : c' < 5)
    (h : m ≠ m' ∨ c ≠ c') : K.ent m c ≠ K.ent m' c' := by
  rw [ent_eq, ent_eq]; exact jg_inj hL (by omega)

omit hL in
theorem ent_slots {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) : K.ent m c ∈ jwSlots K := by
  rw [ent_eq]; exact jg_mem (by omega)

omit hL in
theorem ent_ws {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) : K.ent m c ∈ jwWs K := by
  rw [ent_eq]; exact jg_ws (by omega)

/-- `D`'s slots and `E.x`: written, and distinct. -/
theorem DE_ws : K.D.x ∈ jwWs K ∧ K.D.y ∈ jwWs K ∧ K.D.z ∈ jwWs K ∧ K.E.x ∈ jwWs K := by
  obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
  exact ⟨other_ws dx, other_ws dy, other_ws dz, by rw [hL.Tx]; exact jg_ws (by decide)⟩

theorem DEJ_ne : K.D.x ≠ K.D.y ∧ K.D.x ≠ K.D.z ∧ K.D.y ≠ K.D.z ∧ K.D.x ≠ K.E.x ∧ K.D.y ≠ K.E.x ∧
    K.D.z ≠ K.E.x := by
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
  rw [hL.Tx]
  exact ⟨o 3 4 (by decide) (by decide) (by decide), o 3 5 (by decide) (by decide) (by decide),
    o 4 5 (by decide) (by decide) (by decide), hL.jg_ne (List.mem_append_right _ dx) (by decide),
    hL.jg_ne (List.mem_append_right _ dy) (by decide), hL.jg_ne (List.mem_append_right _ dz) (by decide)⟩

end Slots

/-! ## The prefix products -/

/-- The table's `Z` in a state. -/
abbrev tzJ (K : JacWinCfg) (C : Curve) (base : Addr) (s : State) (j : Nat) : Fe C :=
  tmv C K.M.n base s (K.ent j 2)

/-- After the products `c_2 … c_{i+1}`, from `s₀`: they in their slots, and the
other slots as in `s₀`. -/
structure PreInvJ (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (i : Nat)
    (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) s₀ t
  unch : Unch base (jwW K) s₀.mem t.mem
  mod : ModOkW K.M size C.p t.mem base
  lt : ∀ j, 2 ≤ j → j ≤ i + 1 → wordsVal t.mem base (K.pre j) K.M.n < C.p
  val : ∀ j, 2 ≤ j → j ≤ i + 1 → tmv C K.M.n base t (K.pre j) = cprod (tzJ K C base s₀) j
  same : ∀ x ∈ jwSlots K, (∀ j, 2 ≤ j → j ≤ i + 1 → x ≠ K.pre j) →
    wordsVal t.mem base x K.M.n = wordsVal s₀.mem base x K.M.n

/-- `c_2 … c_16`, from the table's `Z`. -/
theorem prodJ_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr} {P : Point C}
    {s₀ : State} (hs : Scr s₀ base size) (hM : ModOkW K.M size C.p s₀.mem base)
    (hT : JTblOk K C base P 16 s₀) :
    WP isa (fprogB K.M K.prodOps).inline s₀ (PreInvJ K C base size s₀ 15) := by
  rw [fprogB_wp (callOf_of_ne (by rcases hL.n46 with h | h <;> omega)), JacWinCfg.prodOps, fprog, List.flatMap_map]
  have I₀ : PreInvJ K C base size s₀ 0 s₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, fun j h2 h1 => absurd h2 (by omega),
      fun j h2 h1 => absurd h2 (by omega), fun _ _ _ => rfl⟩
  refine block_range_ok (N := 15) (fun i hi t I => ?_) 15 (Nat.le_refl _) s₀ I₀
  -- `Z_{i+2}` is as at `s₀`.
  have zS := ent_slots (K := K) (m := i + 2) (c := 2) (by omega) (by omega) (by decide)
  have ez : wordsVal t.mem base (K.ent (i + 2) 2) K.M.n = wordsVal s₀.mem base (K.ent (i + 2) 2) K.M.n :=
    I.same _ zS fun j h2 hj e => (pre_ne_ent hL (m := j) (by omega) (by omega) (m' := i + 2) (by omega)
      (by omega)).2.2 h2 e.symm
  have ltb : wordsVal t.mem base (K.ent (i + 2) 2) K.M.n < C.p := by
    rw [ez]; exact (hT (i + 2) (by omega) (by omega)).lt 2 (by decide)
  have va : wordsVal t.mem base (K.pre (i + 1)) K.M.n < C.p ∧
      tmv C K.M.n base t (K.pre (i + 1)) = cprod (tzJ K C base s₀) (i + 1) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have e : wordsVal t.mem base (K.pre 1) K.M.n = wordsVal s₀.mem base (K.ent 1 2) K.M.n :=
        I.same _ (pre_slots (K := K) (m := 1) (Nat.le_refl _) (by omega)) fun j h2 hj e =>
          absurd (pre_inj hL (Nat.le_refl _) (by omega) (by omega) (by omega) e) (by omega)
      refine ⟨by rw [e]; exact (hT 1 (Nat.le_refl _) (by omega)).lt 2 (by decide), ?_⟩
      rw [tmv_congr e]; rfl
    · exact ⟨I.lt _ (by omega) (by omega), I.val _ (by omega) (by omega)⟩
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod (pre_ws (K := K) (m := i + 2) (by omega) (by omega))
    (pre_slots (K := K) (m := i + 1) (by omega) (by omega)) zS va.1 ltb)
    fun u ⟨su, ku, Uu, Mu, lu, vu, eu⟩ => ?_
  have ne : ∀ j, 2 ≤ j → j ≤ i + 1 → K.pre j ≠ K.pre (i + 2) := fun j h2 hj h =>
    absurd (pre_inj hL (by omega) (by omega) (by omega) (by omega) h) (by omega)
  refine ⟨su, I.keep.trans ku, (I.unch.trans Uu).mono jwW_append, Mu, fun j h2 hj => ?_,
    fun j h2 hj => ?_, fun x hx hne => ?_⟩
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [eu _ (pre_slots (K := K) (by omega) (by omega)) (ne j h2 (by omega))]
      exact I.lt j h2 (by omega)
    · obtain rfl : j = i + 2 := by omega
      exact lu
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [tmv_congr (eu _ (pre_slots (K := K) (by omega) (by omega)) (ne j h2 (by omega)))]
      exact I.val j h2 (by omega)
    · obtain rfl : j = i + 2 := by omega
      rw [vu, va.2, tmv_congr ez]
      rfl
  · rw [eu x hx (hne _ (by omega) (by omega))]
    exact I.same x hx fun j h2 hj => hne j h2 (by omega)

/-! ## Back from entry `16` -/

theorem cprod_ne_zero16 (hC : Law C) {Z : Nat → Fe C} (hZ : ∀ j, 1 ≤ j → j ≤ 16 → Z j ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ 16 → cprod Z m ≠ 0
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => hZ 1 (Nat.le_refl _) (by omega)
  | j + 2, _, h16 => hC.mul_ne_zero (cprod_ne_zero16 hC hZ (j + 1) (by omega) (by omega)) (hZ _ (by omega) h16)

/-- The table and the products as the inversion leaves them: `c_1 … c_15`, and
the entries' `X`, `Y`, `Z` (nonzero). -/
structure BackStartJ (K : JacWinCfg) (C : Curve) (base : Addr) (u₀ : State) (X Y Z : Nat → Fe C) : Prop where
  c : ∀ j, 1 ≤ j → j ≤ 15 → wordsVal u₀.mem base (K.pre j) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.pre j) = cprod Z j
  x : ∀ j, 1 ≤ j → j ≤ 16 → wordsVal u₀.mem base (K.ent j 0) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.ent j 0) = X j
  y : ∀ j, 1 ≤ j → j ≤ 16 → wordsVal u₀.mem base (K.ent j 1) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.ent j 1) = Y j
  z : ∀ j, 1 ≤ j → j ≤ 16 → wordsVal u₀.mem base (K.ent j 2) K.M.n < C.p ∧
    tmv C K.M.n base u₀ (K.ent j 2) = Z j
  nz : ∀ j, 1 ≤ j → j ≤ 16 → Z j ≠ 0

/-- What entry `j` holds once done: `X` and `Y` by the square and the cube of
`Z^(p-2)`. -/
def DoneJ (K : JacWinCfg) (C : Curve) (base : Addr) (X Y Z : Nat → Fe C) (t : State) (j : Nat) : Prop :=
  wordsVal t.mem base (K.ent j 0) K.M.n < C.p ∧ wordsVal t.mem base (K.ent j 1) K.M.n < C.p ∧
    tmv C K.M.n base t (K.ent j 0) = X j * (Z j ^ (C.p - 2) * Z j ^ (C.p - 2)) ∧
    tmv C K.M.n base t (K.ent j 1) = Y j * (Z j ^ (C.p - 2) * Z j ^ (C.p - 2) * Z j ^ (C.p - 2))

theorem DoneJ.congr {X Y Z : Nat → Fe C} {base : Addr} {t t' : State} {j : Nat}
    (h : DoneJ K C base X Y Z t j)
    (ex : wordsVal t'.mem base (K.ent j 0) K.M.n = wordsVal t.mem base (K.ent j 0) K.M.n)
    (ey : wordsVal t'.mem base (K.ent j 1) K.M.n = wordsVal t.mem base (K.ent j 1) K.M.n) :
    DoneJ K C base X Y Z t' j :=
  ⟨by rw [ex]; exact h.1, by rw [ey]; exact h.2.1, by rw [tmv_congr ex]; exact h.2.2.1,
    by rw [tmv_congr ey]; exact h.2.2.2⟩

/-- The slots the back substitution writes. -/
def backW (K : JacWinCfg) : List Nat := [K.D.x, K.D.y, K.D.z, K.E.x]

/-- After entries `16 … 17 - i`: `c_{16-i}^(p-2)` in `E.x`, those entries done,
and the other slots but `D`'s and `E.x` as at `u₀`. -/
structure BackInvJ (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (u₀ : State) (X Y Z : Nat → Fe C)
    (i : Nat) (t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) u₀ t
  unch : Unch base (jwW K) u₀.mem t.mem
  mod : ModOkW K.M size C.p t.mem base
  ex_lt : wordsVal t.mem base K.E.x K.M.n < C.p
  ex : tmv C K.M.n base t K.E.x = cprod Z (16 - i) ^ (C.p - 2)
  done : ∀ j, 16 - i < j → j ≤ 16 → DoneJ K C base X Y Z t j
  same : ∀ x ∈ jwSlots K, x ∉ backW K →
    (∀ j, 16 - i < j → j ≤ 16 → x ≠ K.ent j 0 ∧ x ≠ K.ent j 1) →
    wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n

theorem not_backW {x : Nat} (h1 : x ≠ K.D.x) (h2 : x ≠ K.D.y) (h3 : x ≠ K.D.z) (h4 : x ≠ K.E.x) :
    x ∉ backW K := by
  simp only [backW, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h2, h3, h4⟩

/-- Six products writing `D.x`, `E.x`, `D.y`, `X_m`, `D.z`, `Y_m` keep the other slots. -/
theorem keep6 {t t₁ t₂ t₃ t₄ t₅ t₆ : State} {base : Addr} {m : Nat}
    (e₁ : ∀ x ∈ jwSlots K, x ≠ K.D.x → wordsVal t₁.mem base x K.M.n = wordsVal t.mem base x K.M.n)
    (e₂ : ∀ x ∈ jwSlots K, x ≠ K.E.x → wordsVal t₂.mem base x K.M.n = wordsVal t₁.mem base x K.M.n)
    (e₃ : ∀ x ∈ jwSlots K, x ≠ K.D.y → wordsVal t₃.mem base x K.M.n = wordsVal t₂.mem base x K.M.n)
    (e₄ : ∀ x ∈ jwSlots K, x ≠ K.ent m 0 → wordsVal t₄.mem base x K.M.n = wordsVal t₃.mem base x K.M.n)
    (e₅ : ∀ x ∈ jwSlots K, x ≠ K.D.z → wordsVal t₅.mem base x K.M.n = wordsVal t₄.mem base x K.M.n)
    (e₆ : ∀ x ∈ jwSlots K, x ≠ K.ent m 1 → wordsVal t₆.mem base x K.M.n = wordsVal t₅.mem base x K.M.n)
    {x : Nat} (hx : x ∈ jwSlots K) (hb : x ∉ backW K) (h0 : x ≠ K.ent m 0) (h1 : x ≠ K.ent m 1) :
    wordsVal t₆.mem base x K.M.n = wordsVal t.mem base x K.M.n := by
  simp only [backW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  rw [e₆ x hx h1, e₅ x hx hb.2.2.1, e₄ x hx h0, e₃ x hx hb.2.1, e₂ x hx hb.2.2.2, e₁ x hx hb.1]

/-- Entry `m = 16 - i` (`2 ≤ m`). -/
theorem backJ_step (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {base : Addr}
    {u₀ : State} {X Y Z : Nat → Fe C} (B : BackStartJ K C base u₀ X Y Z) {i : Nat} (hi : i < 15) {t : State}
    (I : BackInvJ K C base size u₀ X Y Z i t) :
    WP isa (.block (fprog K.M (K.backOps (16 - i)))) t (BackInvJ K C base size u₀ X Y Z (i + 1)) := by
  generalize hm : 16 - i = m
  have hm2 : 2 ≤ m := by omega
  have hm16 : m ≤ 16 := by omega
  have hmi : 16 - (i + 1) = m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hm1' : 1 ≤ m - 1 := by omega
  have hm15 : m - 1 ≤ 16 := by omega
  have hm15' : m - 1 ≤ 15 := by omega
  obtain ⟨dxy, dxz, dyz, dxe, dye, dze⟩ := DEJ_ne hL
  obtain ⟨Dw, Dyw, Dzw, Ew⟩ := DE_ws hL
  have Ds := ws_mem Dw; have Dys := ws_mem Dyw; have Dzs := ws_mem Dzw; have Es := ws_mem Ew
  have xw := ent_ws (K := K) (m := m) (c := 0) hm1 hm16 (by decide)
  have yw := ent_ws (K := K) (m := m) (c := 1) hm1 hm16 (by decide)
  have zS := ent_slots (K := K) (m := m) (c := 2) hm1 hm16 (by decide)
  have dm := fun c (hc : c < 5) => DE_ent hL (m := m) (c := c) hm1 hm16 hc
  -- What is not done at `t`.
  have nd : ∀ {x}, x ∈ jwSlots K → x ∉ backW K → (∀ j, m < j → j ≤ 16 →
      x ≠ K.ent j 0 ∧ x ≠ K.ent j 1) → wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n :=
    fun hx h1 h3 => I.same _ hx h1 fun j hj hj' => h3 j (by omega_using [hj, hm]) hj'
  have pc := pre_ne_DE hL (m := m - 1) hm1' hm15
  have cS := pre_slots (K := K) (m := m - 1) hm1' hm15
  have ec : wordsVal t.mem base (K.pre (m - 1)) K.M.n = wordsVal u₀.mem base (K.pre (m - 1)) K.M.n :=
    nd cS (not_backW pc.1 pc.2.1 pc.2.2.1 pc.2.2.2) fun j hj hj' =>
      ⟨(pre_ne_ent hL hm1' hm15 (m' := j) (by omega_using [hj, hm1]) hj').1,
        (pre_ne_ent hL hm1' hm15 (m' := j) (by omega_using [hj, hm1]) hj').2.1⟩
  have notB : ∀ c < 5, K.ent m c ∉ backW K := fun c hc =>
    not_backW (dm c hc).1.symm (dm c hc).2.1.symm (dm c hc).2.2.1.symm (dm c hc).2.2.2.symm
  have enem : ∀ c < 5, ∀ j, m < j → j ≤ 16 → K.ent m c ≠ K.ent j 0 ∧ K.ent m c ≠ K.ent j 1 :=
    fun c hc j hj _ => ⟨ent_ne hL hm1 (by omega_using [hj, hm1]) hc (by decide) (Or.inl (by omega_using [hj])),
      ent_ne hL hm1 (by omega_using [hj, hm1]) hc (by decide) (Or.inl (by omega_using [hj]))⟩
  have ez : wordsVal t.mem base (K.ent m 2) K.M.n = wordsVal u₀.mem base (K.ent m 2) K.M.n :=
    nd zS (notB 2 (by decide)) (enem 2 (by decide))
  have ex0 : wordsVal t.mem base (K.ent m 0) K.M.n = wordsVal u₀.mem base (K.ent m 0) K.M.n :=
    nd (ws_mem xw) (notB 0 (by decide)) (enem 0 (by decide))
  have ey0 : wordsVal t.mem base (K.ent m 1) K.M.n = wordsVal u₀.mem base (K.ent m 1) K.M.n :=
    nd (ws_mem yw) (notB 1 (by decide)) (enem 1 (by decide))
  have hcm := cprod_succ Z hm2
  have nz := cprod_ne_zero16 hC B.nz (m - 1) hm1' hm15
  obtain ⟨tr1, tr2⟩ := trick_step hC nz (B.nz m hm1 hm16)
  rw [← hcm] at tr1 tr2
  rw [JacWinCfg.backOps, fprog_cons, WP.block_append_iff]
  -- `D.x = E.x c_{m-1}`.
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod Dw Es cS I.ex_lt
    (by rw [ec]; exact (B.c _ hm1' hm15').1)) fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  have ex₁ := e₁ _ Es dxe.symm
  -- `E.x = E.x Z_m`.
  refine WP.mono (slotMulJ_ok hL hp s₁ M₁ Ew Es zS (by rw [ex₁]; exact I.ex_lt)
    (by rw [e₁ _ zS (dm 2 (by decide)).1.symm, ez]; exact (B.z m hm1 hm16).1))
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  have dx₂ := e₂ _ Ds dxe
  -- `D.y = D.x²`.
  refine WP.mono (slotMulJ_ok hL hp s₂ M₂ Dyw Ds Ds (by rw [dx₂]; exact l₁) (by rw [dx₂]; exact l₁))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  have xx₃ : wordsVal t₃.mem base (K.ent m 0) K.M.n = wordsVal u₀.mem base (K.ent m 0) K.M.n := by
    rw [e₃ _ (ws_mem xw) (dm 0 (by decide)).2.1.symm, e₂ _ (ws_mem xw) (dm 0 (by decide)).2.2.2.symm,
      e₁ _ (ws_mem xw) (dm 0 (by decide)).1.symm, ex0]
  -- `X_m = X_m D.y`.
  refine WP.mono (slotMulJ_ok hL hp s₃ M₃ xw (ws_mem xw) Dys
    (by rw [xx₃]; exact (B.x m hm1 hm16).1) l₃)
    fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  have dy₄ := e₄ _ Dys (dm 0 (by decide)).2.1
  have dx₄ : wordsVal t₄.mem base K.D.x K.M.n = wordsVal t₂.mem base K.D.x K.M.n := by
    rw [e₄ _ Ds (dm 0 (by decide)).1, e₃ _ Ds dxy]
  -- `D.z = D.y D.x`.
  refine WP.mono (slotMulJ_ok hL hp s₄ M₄ Dzw Dys Ds (by rw [dy₄]; exact l₃) (by rw [dx₄, dx₂]; exact l₁))
    fun t₅ ⟨s₅, k₅, U₅, M₅, l₅, v₅, e₅⟩ => ?_
  rw [fprog_cons, fprog, List.flatMap_nil, List.append_nil]
  have yy₅ : wordsVal t₅.mem base (K.ent m 1) K.M.n = wordsVal u₀.mem base (K.ent m 1) K.M.n := by
    rw [e₅ _ (ws_mem yw) (dm 1 (by decide)).2.2.1.symm,
      e₄ _ (ws_mem yw) (ent_ne hL hm1 hm1 (by decide) (by decide) (Or.inr (by decide))),
      e₃ _ (ws_mem yw) (dm 1 (by decide)).2.1.symm, e₂ _ (ws_mem yw) (dm 1 (by decide)).2.2.2.symm,
      e₁ _ (ws_mem yw) (dm 1 (by decide)).1.symm, ey0]
  -- `Y_m = Y_m D.z`.
  refine WP.mono (slotMulJ_ok hL hp s₅ M₅ yw (ws_mem yw) Dzs
    (by rw [yy₅]; exact (B.y m hm1 hm16).1) l₅)
    fun t₆ ⟨s₆, k₆, U₆, M₆, l₆, v₆, e₆⟩ => ?_
  have k6 := fun {x} (hx : x ∈ jwSlots K) (hb : x ∉ backW K) (h0 : x ≠ K.ent m 0) (h1 : x ≠ K.ent m 1) =>
    keep6 (t := t) (m := m) e₁ e₂ e₃ e₄ e₅ e₆ hx hb h0 h1
  have vD : tmv C K.M.n base t₁ K.D.x = Z m ^ (C.p - 2) := by
    rw [v₁, I.ex, hm, tmv_congr ec, (B.c _ hm1' hm15').2]; exact tr1
  have vE : tmv C K.M.n base t₂ K.E.x = cprod Z (m - 1) ^ (C.p - 2) := by
    rw [v₂, tmv_congr ex₁, I.ex, hm, tmv_congr (e₁ _ zS (dm 2 (by decide)).1.symm), tmv_congr ez,
      (B.z m hm1 hm16).2]; exact tr2
  have ex₆ : wordsVal t₆.mem base K.E.x K.M.n = wordsVal t₂.mem base K.E.x K.M.n := by
    rw [e₆ _ Es (dm 1 (by decide)).2.2.2, e₅ _ Es dze.symm, e₄ _ Es (dm 0 (by decide)).2.2.2,
      e₃ _ Es dye.symm]
  have xx₆ : wordsVal t₆.mem base (K.ent m 0) K.M.n = wordsVal t₄.mem base (K.ent m 0) K.M.n := by
    rw [e₆ _ (ws_mem xw) (ent_ne hL hm1 hm1 (by decide) (by decide) (Or.inr (by decide))),
      e₅ _ (ws_mem xw) (dm 0 (by decide)).2.2.1.symm]
  have vDy : tmv C K.M.n base t₃ K.D.y = Z m ^ (C.p - 2) * Z m ^ (C.p - 2) := by
    rw [v₃, tmv_congr dx₂, vD]
  have vDz : tmv C K.M.n base t₅ K.D.z = Z m ^ (C.p - 2) * Z m ^ (C.p - 2) * Z m ^ (C.p - 2) := by
    rw [v₅, tmv_congr dy₄, vDy, tmv_congr dx₄, tmv_congr dx₂, vD]
  refine ⟨s₆, I.keep.trans (k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆))))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆)))))).mono fun w hw => ?_, M₆,
    by rw [ex₆]; exact l₂, by rw [hmi, tmv_congr ex₆, vE], fun j hj hj16 => ?_, fun x hx hb h3 => ?_⟩
  · simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge m j with hj' | hj'
    · have tj := fun c (hc : c < 5) => DE_ent hL (m := j) (c := c) (by omega_using [hj']) hj16 hc
      have nb := fun c (hc : c < 5) =>
        not_backW (tj c hc).1.symm (tj c hc).2.1.symm (tj c hc).2.2.1.symm (tj c hc).2.2.2.symm
      exact (I.done j (by omega_using [hj', hm]) hj16).congr
        (k6 (ent_slots (K := K) (by omega_using [hj', hm1]) hj16 (by decide)) (nb 0 (by decide))
          (ent_ne hL (by omega_using [hj', hm1]) hm1 (by decide) (by decide) (Or.inl (by omega_using [hj'])))
          (ent_ne hL (by omega_using [hj', hm1]) hm1 (by decide) (by decide) (Or.inl (by omega_using [hj']))))
        (k6 (ent_slots (K := K) (by omega_using [hj', hm1]) hj16 (by decide)) (nb 1 (by decide))
          (ent_ne hL (by omega_using [hj', hm1]) hm1 (by decide) (by decide) (Or.inl (by omega_using [hj'])))
          (ent_ne hL (by omega_using [hj', hm1]) hm1 (by decide) (by decide) (Or.inl (by omega_using [hj']))))
    · obtain rfl : j = m := by omega_using [hj', hj, hmi]
      refine ⟨by rw [xx₆]; exact l₄, l₆, ?_, ?_⟩
      · rw [tmv_congr xx₆, v₄, tmv_congr xx₃, (B.x j hm1 hj16).2, vDy]
      · rw [v₆, tmv_congr yy₅, (B.y j hm1 hj16).2, vDz]
  · have hm' := h3 m (by omega_using [hmi, hm2]) hm16
    rw [k6 hx hb hm'.1 hm'.2]
    exact I.same x hx hb fun j hj hj' => h3 j (by omega_using [hj]) hj'

theorem fprog_flatMapJ (M : Mod) (l : List Nat) (g : Nat → List FOp) :
    fprog M (l.flatMap g) = l.flatMap fun i => fprog M (g i) := by
  simp only [fprog, List.flatMap_assoc]

/-- The entries' `X` and `Y` by the square and the cube of their
`Z^(p-2)`, from `c_16^(p-2)` in `E.x`. -/
theorem backJ_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {base : Addr}
    {u₀ : State} {X Y Z : Nat → Fe C} (B : BackStartJ K C base u₀ X Y Z) (hs : Scr u₀ base size)
    (hM : ModOkW K.M size C.p u₀.mem base) (hel : wordsVal u₀.mem base K.E.x K.M.n < C.p)
    (hev : tmv C K.M.n base u₀ K.E.x = cprod Z 16 ^ (C.p - 2)) :
    WP isa (fprogB K.M K.normOps).inline u₀ fun t => Scr t base size ∧
      KeepRegs (clob K.M.n) u₀ t ∧ Unch base (jwW K) u₀.mem t.mem ∧ ModOkW K.M size C.p t.mem base ∧
      ∀ j, 1 ≤ j → j ≤ 16 → DoneJ K C base X Y Z t j := by
  rw [fprogB_wp (callOf_of_ne (by rcases hL.n46 with h | h <;> omega)), JacWinCfg.normOps, fprog_append, fprog_flatMapJ, WP.block_append_iff]
  have I₀ : BackInvJ K C base size u₀ X Y Z 0 u₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, hel, hev, fun j hj hj' => absurd hj' (by omega),
      fun _ _ _ _ => rfl⟩
  refine WP.mono (block_range_ok (N := 15) (fun i hi t I => backJ_step hL hp hC B hi I) 15 (Nat.le_refl _) u₀ I₀)
    fun t I => ?_
  obtain ⟨dxy, dxz, dyz, dxe, dye, dze⟩ := DEJ_ne hL
  obtain ⟨Dw, Dyw, Dzw, Ew⟩ := DE_ws hL
  have Ds := ws_mem Dw; have Dys := ws_mem Dyw; have Dzs := ws_mem Dzw; have Es := ws_mem Ew
  have xw := ent_ws (K := K) (m := 1) (c := 0) (Nat.le_refl _) (by omega) (by decide)
  have yw := ent_ws (K := K) (m := 1) (c := 1) (Nat.le_refl _) (by omega) (by decide)
  have d1 := fun c (hc : c < 5) => DE_ent hL (m := 1) (c := c) (Nat.le_refl _) (by omega) hc
  have nb := fun c (hc : c < 5) =>
    not_backW (d1 c hc).1.symm (d1 c hc).2.1.symm (d1 c hc).2.2.1.symm (d1 c hc).2.2.2.symm
  have ex1 : wordsVal t.mem base (K.ent 1 0) K.M.n = wordsVal u₀.mem base (K.ent 1 0) K.M.n :=
    I.same _ (ws_mem xw) (nb 0 (by decide)) fun j hj _ =>
      ⟨ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega)),
        ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega))⟩
  have ey1 : wordsVal t.mem base (K.ent 1 1) K.M.n = wordsVal u₀.mem base (K.ent 1 1) K.M.n :=
    I.same _ (ws_mem yw) (nb 1 (by decide)) fun j hj _ =>
      ⟨ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega)),
        ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega))⟩
  have hex : tmv C K.M.n base t K.E.x = Z 1 ^ (C.p - 2) := by rw [I.ex]; rfl
  rw [fprog_cons, WP.block_append_iff]
  -- `D.y = E.x²`.
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod Dyw Es Es I.ex_lt I.ex_lt)
    fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  -- `X_1 = X_1 D.y`.
  refine WP.mono (slotMulJ_ok hL hp s₁ M₁ xw (ws_mem xw) Dys
    (by rw [e₁ _ (ws_mem xw) (d1 0 (by decide)).2.1.symm, ex1]; exact (B.x 1 (Nat.le_refl _) (by omega)).1) l₁)
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  rw [fprog_cons, WP.block_append_iff]
  have dy₂ := e₂ _ Dys (d1 0 (by decide)).2.1
  have ee₂ : wordsVal t₂.mem base K.E.x K.M.n = wordsVal t.mem base K.E.x K.M.n := by
    rw [e₂ _ Es (d1 0 (by decide)).2.2.2, e₁ _ Es dye.symm]
  -- `D.z = D.y E.x`.
  refine WP.mono (slotMulJ_ok hL hp s₂ M₂ Dzw Dys Es (by rw [dy₂]; exact l₁) (by rw [ee₂]; exact I.ex_lt))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_
  rw [fprog_cons, fprog, List.flatMap_nil, List.append_nil]
  have yy₃ : wordsVal t₃.mem base (K.ent 1 1) K.M.n = wordsVal t.mem base (K.ent 1 1) K.M.n := by
    rw [e₃ _ (ws_mem yw) (d1 1 (by decide)).2.2.1.symm,
      e₂ _ (ws_mem yw) (ent_ne hL (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide) (Or.inr (by decide))),
      e₁ _ (ws_mem yw) (d1 1 (by decide)).2.1.symm]
  -- `Y_1 = Y_1 D.z`.
  refine WP.mono (slotMulJ_ok hL hp s₃ M₃ yw (ws_mem yw) Dzs
    (by rw [yy₃, ey1]; exact (B.y 1 (Nat.le_refl _) (by omega)).1) l₃)
    fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  have k4 : ∀ x ∈ jwSlots K, x ∉ backW K → x ≠ K.ent 1 0 → x ≠ K.ent 1 1 →
      wordsVal t₄.mem base x K.M.n = wordsVal t.mem base x K.M.n := fun x hx hb h0 h1 => by
    simp only [backW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [e₄ x hx h1, e₃ x hx hb.2.2.1, e₂ x hx h0, e₁ x hx hb.2.1]
  refine ⟨s₄, I.keep.trans (k₁.trans (k₂.trans (k₃.trans k₄))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans U₄)))).mono fun w hw => ?_, M₄, fun j hj hj16 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge 1 j with hj' | hj'
    · have tj := fun c (hc : c < 5) => DE_ent hL (m := j) (c := c) (by omega) hj16 hc
      have nbj := fun c (hc : c < 5) =>
        not_backW (tj c hc).1.symm (tj c hc).2.1.symm (tj c hc).2.2.1.symm (tj c hc).2.2.2.symm
      exact (I.done j (by omega) hj16).congr
        (k4 _ (ent_slots (K := K) (by omega) hj16 (by decide)) (nbj 0 (by decide))
          (ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega)))
          (ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega))))
        (k4 _ (ent_slots (K := K) (by omega) hj16 (by decide)) (nbj 1 (by decide))
          (ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega)))
          (ent_ne hL (by omega) (by omega) (by decide) (by decide) (Or.inl (by omega))))
    · obtain rfl : j = 1 := by omega
      have xx₄ : wordsVal t₄.mem base (K.ent 1 0) K.M.n = wordsVal t₂.mem base (K.ent 1 0) K.M.n := by
        rw [e₄ _ (ws_mem xw) (ent_ne hL (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide)
          (Or.inr (by decide))), e₃ _ (ws_mem xw) (d1 0 (by decide)).2.2.1.symm]
      refine ⟨by rw [xx₄]; exact l₂, l₄, ?_, ?_⟩
      · rw [tmv_congr xx₄, v₂, tmv_congr (e₁ _ (ws_mem xw) (d1 0 (by decide)).2.1.symm), tmv_congr ex1,
          (B.x 1 (Nat.le_refl _) (by omega)).2, v₁, hex]
      · rw [v₄, tmv_congr yy₃, tmv_congr ey1, (B.y 1 (Nat.le_refl _) (by omega)).2, v₃, tmv_congr dy₂, v₁,
          tmv_congr ee₂, hex]

/-! ## Every `Z` one -/

/-- Entries' `Z`, `Z²` and `Z³` set to `x`: the first `i` of the 48. -/
theorem onesJ_ok (hL : JacWinLay K size) {base : Addr} {x : Nat} (hx : x < 2 ^ (64 * K.M.n)) :
    ∀ i ≤ 48, ∀ s : State, Scr s base size →
      WP isa (.block ((List.range i).flatMap fun j => setConst K.M.n (K.ent (j / 3 + 1) (2 + j % 3)) x)) s
        fun t => Scr t base size ∧ KeepRegs [.rax] s t ∧ Unch base (jwW K) s.mem t.mem ∧
        (∀ j < i, wordsVal t.mem base (K.ent (j / 3 + 1) (2 + j % 3)) K.M.n = x) ∧
        ∀ y ∈ jwSlots K, (∀ j < i, y ≠ K.ent (j / 3 + 1) (2 + j % 3)) →
          wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n := by
  intro i hi s hs
  refine block_range_ok (N := 48) (Inv := fun i t => Scr t base size ∧ KeepRegs [.rax] s t ∧
      Unch base (jwW K) s.mem t.mem ∧ (∀ j < i, wordsVal t.mem base (K.ent (j / 3 + 1) (2 + j % 3)) K.M.n = x) ∧
      ∀ y ∈ jwSlots K, (∀ j < i, y ≠ K.ent (j / 3 + 1) (2 + j % 3)) →
        wordsVal t.mem base y K.M.n = wordsVal s.mem base y K.M.n)
    (fun i hi t ⟨st, kt, Ut, vt, et⟩ => ?_) i hi s
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, fun j h0 => absurd h0 (by omega), fun _ _ _ => rfl⟩
  have zs := ent_slots (K := K) (m := i / 3 + 1) (c := 2 + i % 3) (by omega) (by omega) (by omega)
  have zw := ent_ws (K := K) (m := i / 3 + 1) (c := 2 + i % 3) (by omega) (by omega) (by omega)
  refine WP.mono (setConst_ok st (n := K.M.n) (o := K.ent (i / 3 + 1) (2 + i % 3)) (hL.lay.le _ zs) hx)
    fun u ⟨eu, ku, Ou⟩ => ?_
  have hn := st.nowrap
  have same : ∀ y ∈ jwSlots K, y ≠ K.ent (i / 3 + 1) (2 + i % 3) →
      wordsVal u.mem base y K.M.n = wordsVal t.mem base y K.M.n := fun y hy hne =>
    Ou.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact hL.lay.apart y _ hy zs hne) (by have := hL.lay.le y hy; omega)
  refine ⟨st.of_keepRegs ku (by decide), kt.trans ku, (Ut.trans Ou.unch).mono fun w hw => ?_,
    fun j hj => ?_, fun y hy hne => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · rw [List.mem_singleton.mp hw]; exact mem_jwW_ws zw
  · rcases Nat.lt_or_ge j i with hj' | hj'
    · rw [same _ (ent_slots (K := K) (by omega) (by omega) (by omega))
        (ent_ne hL (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact vt j hj'
    · obtain rfl : j = i := by omega
      exact eu
  · rw [same y hy (hne _ (by omega))]
    exact et y hy fun j hj => hne j (by omega)

/-! ## The table -/

/-- What the inversion `inv` does: `E.x = R.z^(p-2)`, writing `IW`: `E.x`, the
temporary area, and areas apart from the modulus and the window's slots and
table of bits. -/
structure InvSpecJ (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (inv : Prog isa)
    (IW : List (Nat × Nat)) : Prop where
  ok : ∀ t : State, Scr t base size → ModOkW K.M size C.p t.mem base →
    wordsVal t.mem base K.R.z K.M.n < C.p → WP isa inv.inline t fun t' =>
      KeepRegs (invClob K.M.n) t t' ∧ Unch base IW t.mem t'.mem ∧
      wordsVal t'.mem base K.E.x K.M.n < C.p ∧
      tmv C K.M.n base t' K.E.x = tmv C K.M.n base t K.R.z ^ (C.p - 2)
  w : ∀ w ∈ IW, w = (K.E.x, 8 * K.M.n) ∨ w = (K.M.tmp, 8 * K.M.n) ∨
    ((K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo) ∧
      ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
  bits : ∀ w ∈ IW, K.bits + 5 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

theorem InvSpecJ.same {inv : Prog isa} {base : Addr} {IW : List (Nat × Nat)}
    (h : InvSpecJ K C base size inv IW) (hL : JacWinLay K size) {m m' : Mem}
    (hU : Unch base IW m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat} (hx : x ∈ jwSlots K)
    (hne : x ≠ K.E.x) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (fun w hw => by
    rcases h.w w hw with rfl | rfl | ⟨-, h⟩
    · exact hL.lay.apart x _ hx (by rw [hL.Tx]; exact jg_mem (by decide)) hne
    · exact hL.lay.tmp x hx
    · exact h x hx) (by have := hL.lay.le x hx; omega)

theorem InvSpecJ.mo {inv : Prog isa} {base : Addr} {IW : List (Nat × Nat)}
    (h : InvSpecJ K C base size inv IW) (hL : JacWinLay K size) {mem : Mem}
    (hM : ModOkW K.M size C.p mem base) : ∀ w ∈ IW, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  rcases h.w w hw with rfl | rfl | ⟨h, -⟩
  · have := hL.lay.mo K.E.x (by rw [hL.Tx]; exact jg_mem (by decide)); dsimp only; omega
  · have := hM.sep; dsimp only; omega
  · exact h

/-- Entries `1 … 16` hold `[m]P` with `Z` one: the table `normA` leaves. -/
def JTblOne (K : JacWinCfg) (base : Addr) (s : State) : Prop :=
  ∀ m, 1 ≤ m → m ≤ 16 → wordsVal s.mem base (entS K m 2) K.M.n = K.one

/-- The table into affine coordinates: still Jacobian triples of `[m]P` with
their powers, with `Z` (and so `Z²`, `Z³`) one. -/
theorem normA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr} (hI : InvSpecJ K C base size inv IW) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hT : JTblOk K C base P 16 s) :
    WP isa (K.normA inv).inline s fun s' => Scr s' base size ∧ KeepRegs (invClob K.M.n) s s' ∧
      Unch base (jwW K ++ IW) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      JTblOk K C base P 16 s' ∧ JTblOne K base s' := by
  have hn := hs.nowrap
  have h1p : (1 : Fe C) ≠ 0 := hC.one_ne_zero
  rw [JacWinCfg.normA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (prodJ_ok hL hp hs hM hT) fun t I => ?_)
  refine WP.seq (WP.mono (hI.ok t I.scr I.mod (I.lt 16 (by decide) (by decide)))
    fun u₀ ⟨Ku, Uu, lu, vu⟩ => ?_)
  have hsu := I.scr.of_keepRegs Ku (rdi_not_invClob' _)
  have Mu := I.mod.unch Uu (hI.mo hL I.mod) hn
  -- The table and the products at `u₀`.
  have tsame : ∀ {m c}, 1 ≤ m → m ≤ 16 → c < 3 → wordsVal u₀.mem base (K.ent m c) K.M.n =
      wordsVal s.mem base (K.ent m c) K.M.n := @fun m c h1 h16 hc => by
    have ys := ent_slots (K := K) h1 h16 (show c < 5 by omega)
    rw [hI.same hL Uu hn ys (DE_ent hL h1 h16 (show c < 5 by omega)).2.2.2.symm]
    refine I.same _ ys fun j h2 hj e => ?_
    have pe := pre_ne_ent hL (m := j) (by omega) (by omega) (m' := m) h1 h16
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · exact pe.1 e.symm
    · exact pe.2.1 e.symm
    · exact pe.2.2 h2 e.symm
  have B : BackStartJ K C base u₀ (fun j => tmv C K.M.n base s (K.ent j 0))
      (fun j => tmv C K.M.n base s (K.ent j 1)) (tzJ K C base s) := by
    refine ⟨fun j h1 h15 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_⟩
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · obtain rfl : j = 1 := by omega
        have e := tsame (m := 1) (c := 2) (Nat.le_refl _) (by omega) (by decide)
        have pe : K.pre 1 = K.ent 1 2 := rfl
        rw [pe, e, tmv_congr e]
        exact ⟨(hT 1 (Nat.le_refl _) (by omega)).lt 2 (by decide), rfl⟩
      · have e := hI.same hL Uu hn (pre_slots (K := K) (by omega) (by omega))
          (pre_ne_DE hL (m := j) (by omega) (by omega)).2.2.2
        rw [e, tmv_congr e]
        exact ⟨I.lt j hj (by omega), I.val j hj (by omega)⟩
    · have e := tsame (c := 0) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 0 (by decide), rfl⟩
    · have e := tsame (c := 1) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 1 (by decide), rfl⟩
    · have e := tsame (c := 2) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 2 (by decide), rfl⟩
    · exact (hT j h1 h16).z
  have hev : tmv C K.M.n base u₀ K.E.x = cprod (tzJ K C base s) 16 ^ (C.p - 2) := by
    rw [vu]; exact congrArg (· ^ (C.p - 2)) (I.val 16 (by decide) (Nat.le_refl _))
  refine WP.seq (WP.mono (backJ_ok hL hp hC B hsu Mu lu hev) fun v ⟨sv, kv, Uv, Mv, dv⟩ => ?_)
  refine WP.mono (onesJ_ok hL (x := K.one) (Nat.lt_trans hone_lt hpn) 48 (Nat.le_refl _) v sv)
    fun w ⟨sw, kw, Uw, ow, ew⟩ => ?_
  have c1 : ∀ r ∈ [Reg.rax], r ∈ invClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [invClob, powClob, clob]
  have c2 : ∀ r ∈ clob K.M.n, r ∈ invClob K.M.n := fun r h =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have U : Unch base (jwW K ++ IW) s.mem w.mem :=
    (I.unch.trans (Uu.trans (Uv.trans Uw))).mono fun x hx => by
      simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx | hx | hx <;> simp [hx]
  -- `Z`, `Z²`, `Z³` one.
  have one3 : ∀ m, 1 ≤ m → m ≤ 16 → ∀ c, 2 ≤ c → c < 5 → wordsVal w.mem base (K.ent m c) K.M.n = K.one :=
    fun m h1 h16 c h2 h5 => by
      have e := ow (3 * (m - 1) + (c - 2)) (by omega)
      rwa [show (3 * (m - 1) + (c - 2)) / 3 + 1 = m by omega,
        show 2 + (3 * (m - 1) + (c - 2)) % 3 = c by omega] at e
  have xy : ∀ m, 1 ≤ m → m ≤ 16 → ∀ c < 2, wordsVal w.mem base (K.ent m c) K.M.n =
      wordsVal v.mem base (K.ent m c) K.M.n := fun m h1 h16 c hc =>
    ew _ (ent_slots (K := K) h1 h16 (by omega)) fun j hj =>
      ent_ne hL h1 (by omega) (by omega) (by omega) (Or.inr (by omega))
  refine ⟨sw, ((I.keep.mono c2).trans Ku).trans ((kv.mono c2).trans (kw.mono c1)), U,
    Mv.unch Uw (hL.w_mo Mv) hn, fun m h1 h16 => ?_, fun m h1 h16 => one3 m h1 h16 2 (by decide) (by decide)⟩
  obtain ⟨l0, l1, v0, v1⟩ := dv m h1 h16
  have ex := xy m h1 h16 0 (by decide)
  have ey := xy m h1 h16 1 (by decide)
  have to1 : ∀ c, 2 ≤ c → c < 5 → tmv C K.M.n base w (K.ent m c) = 1 := fun c h2 h5 => by
    show toM _ _ _ = 1; rw [one3 m h1 h16 c h2 h5]; exact hone
  have J : InvJ C (tmv C K.M.n base s (K.ent m 0)) (tmv C K.M.n base s (K.ent m 1))
      (tmv C K.M.n base s (entS K m 2)) (mul m P) := (hT m h1 h16).jac
  have Z0 := (hT m h1 h16).z
  dsimp only at v0 v1
  generalize hz : tmv C K.M.n base s (entS K m 2) = Z at J Z0
  have hz' : tzJ K C base s m = Z := hz
  rw [hz'] at v0 v1
  have hf := hC.fermat Z0
  generalize Z ^ (C.p - 2) = zi at v0 v1 hf
  have zi0 : zi ≠ 0 := fun h => h1p (by rw [← hf, h]; grind)
  refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
  · rcases (show c = 0 ∨ c = 1 ∨ (2 ≤ c ∧ c < 5) by omega) with rfl | rfl | ⟨h2, h5⟩
    · show wordsVal _ base (K.ent m 0) _ < _; rw [ex]; exact l0
    · show wordsVal _ base (K.ent m 1) _ < _; rw [ey]; exact l1
    · show wordsVal _ base (K.ent m c) _ < _; rw [one3 m h1 h16 c h2 h5]; exact hone_lt
  · show InvJ C (tmv C K.M.n base w (K.ent m 0)) (tmv C K.M.n base w (K.ent m 1))
      (tmv C K.M.n base w (K.ent m 2)) _
    rw [tmv_congr ex, tmv_congr ey, v0, v1, to1 2 (by decide) (by decide)]
    exact J.rescale hC zi0 h1p (by grind) (by grind) (by grind)
  · show tmv C K.M.n base w (K.ent m 2) ≠ 0
    rw [to1 2 (by decide) (by decide)]; exact h1p
  · show tmv C K.M.n base w (K.ent m 3) = tmv C K.M.n base w (K.ent m 2) * tmv C K.M.n base w (K.ent m 2)
    rw [to1 3 (by decide) (by decide), to1 2 (by decide) (by decide)]; grind
  · show tmv C K.M.n base w (K.ent m 4) = tmv C K.M.n base w (K.ent m 3) * tmv C K.M.n base w (K.ent m 2)
    rw [to1 4 (by decide) (by decide), to1 3 (by decide) (by decide), to1 2 (by decide) (by decide)]; grind

end VG.Proof.Weierstrass.X86_64
