module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.JacCoZ

/-! ### `Weierstrass.X86_64.WinJacNorm`, which this module and modules that import it used -/

section

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

@[expose] public section

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
    WP isa (opProg K.M (.mul o a b)).inline s fun s' => Scr s' base size ∧
      KeepRegs (clob K.M.n) s s' ∧ Unch base (jwW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧ wordsVal s'.mem base o K.M.n < C.p ∧
      tmv C K.M.n base s' o = tmv C K.M.n base s a * tmv C K.M.n base s b ∧
      ∀ x ∈ jwSlots K, x ≠ o → wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
  obtain I : Inv K.M base size C.p (· ∈ jwSlots K) [a, b] (tmv C K.M.n base s) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hla
      · exact hlb
  obtain hSo : o ∈ jwSlots K := ws_mem ho
  refine WP.mono (opProg_ok hL.lay hp I (op := .mul o a b) (fun x hx => by
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hSo
      · exact ha
      · exact hb)
    (fun x hx => hx)) fun s' ⟨k, I'⟩ => ?_
  obtain U : Unch base [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem :=
    fun x hx => k.mem x (hx _ (List.mem_cons_self ..)) (hx (K.M.tmp, 8 * K.M.n) (by simp))
  refine ⟨I'.scr, ⟨k.gpr, k.rd, k.wr⟩, U.mono fun w hw => ?_, I'.mod, I'.lt o (List.mem_cons_self ..),
    ?_, fun x hx hxo => U.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hx; have := hs.nowrap; omega_arith)⟩
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

theorem fprogB_single (M : Mod) (op : FOp) : fprogB M [op] = opProg M op := rfl

theorem map_eq_flatMapJ (l : List Nat) (f : Nat → FOp) : l.map f = l.flatMap fun i => [f i] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatMap_cons, ih, List.singleton_append]

theorem jwW_append : ∀ w ∈ jwW K ++ jwW K, w ∈ jwW K := fun _ hw =>
  (List.mem_append.mp hw).elim id id

/-! ## The slots -/

/-- Grid slots of distinct indices are distinct. -/
theorem jg_inj (hL : JacWinLay K size) {i j : Nat} (h : i ≠ j) : jg K i ≠ jg K j := by
  have := hL.n0
  rcases jg_apart K h with h | h <;> omega_arith

theorem ent_eq (K : JacWinCfg) (m c : Nat) : K.ent m c = jg K (5 * (m - 1) + c) := rfl

/-- The index in the grid of `c_m`'s slot, `m < 16`. -/
def preG (m : Nat) : Nat := if m = 1 then 2 else 5 * (m - 1) + 3

theorem pre_eq (K : JacWinCfg) {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) : K.pre m = jg K (preG m) := by
  unfold JacWinCfg.pre preG
  by_cases h : m = 1
  · subst h; rfl
  · simp only [h, show ¬ m = 16 by omega_arith, ↓reduceIte]; rfl

theorem pre_16 (K : JacWinCfg) : K.pre 16 = K.R.z := rfl

theorem preG_lt {m : Nat} (h15 : m ≤ 15) : preG m < 80 := by unfold preG; split <;> omega_arith

section Slots
variable (hL : JacWinLay K size)
include hL

omit hL in
theorem RzD : K.R.z ∈ jwOther K ∧ K.D.x ∈ jwOther K ∧ K.D.y ∈ jwOther K ∧ K.D.z ∈ jwOther K := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> jw_mem

omit hL in
theorem pre_slots {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) : K.pre m ∈ jwSlots K := by
  rcases Nat.lt_or_ge m 16 with h | h
  · rw [pre_eq K h1 (by omega_arith)]; exact jg_mem (by have := preG_lt (m := m) (by omega_arith); omega_arith)
  · obtain rfl : m = 16 := by omega_arith
    exact other_mem (RzD (K := K)).1

omit hL in
theorem pre_ws {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) : K.pre m ∈ jwWs K := by
  rcases Nat.lt_or_ge m 16 with h | h
  · rw [pre_eq K h1 (by omega_arith)]; exact jg_ws (by have := preG_lt (m := m) (by omega_arith); omega_arith)
  · obtain rfl : m = 16 := by omega_arith
    exact other_ws (RzD (K := K)).1

theorem pre_inj {m m' : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (h1' : 1 ≤ m') (h16' : m' ≤ 16)
    (h : K.pre m = K.pre m') : m = m' := by
  refine Classical.byContradiction fun hne => ?_
  obtain g : ∀ {m}, 1 ≤ m → m ≤ 15 → K.R.z ≠ K.pre m := fun h1 h15 => by
    rw [pre_eq K h1 h15]
    exact hL.jg_ne (List.mem_append_right _ (RzD (K := K)).1) (by have := preG_lt (m := _) h15; omega_arith)
  rcases Nat.lt_or_ge m 16 with hm | hm <;> rcases Nat.lt_or_ge m' 16 with hm' | hm'
  · rw [pre_eq K h1 (by omega_arith), pre_eq K h1' (by omega_arith)] at h
    refine jg_inj hL ?_ h
    unfold preG; split <;> split <;> omega_arith
  · obtain rfl : m' = 16 := by omega_arith
    exact g h1 (by omega_arith) (h.trans (pre_16 K)).symm
  · obtain rfl : m = 16 := by omega_arith
    exact g h1' (by omega_arith) ((pre_16 K).symm.trans h)
  · exact hne (by omega_arith)

/-- `c_m`'s slot is not `D`'s or `E.x`. -/
theorem pre_ne_DE {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) :
    K.pre m ≠ K.D.x ∧ K.pre m ≠ K.D.y ∧ K.pre m ≠ K.D.z ∧ K.pre m ≠ K.E.x := by
  obtain o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  rcases Nat.lt_or_ge m 16 with hm | hm
  · rw [pre_eq K h1 (by omega_arith)]
    obtain hg := preG_lt (m := m) (by omega_arith)
    obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
    refine ⟨fun e => hL.jg_ne (List.mem_append_right _ dx) (by omega_arith) e.symm,
      fun e => hL.jg_ne (List.mem_append_right _ dy) (by omega_arith) e.symm,
      fun e => hL.jg_ne (List.mem_append_right _ dz) (by omega_arith) e.symm, ?_⟩
    rw [hL.Tx]; exact jg_inj hL (by omega_arith)
  · obtain rfl : m = 16 := by omega_arith
    rw [pre_16]
    refine ⟨o 2 3 (by decide) (by decide) (by decide), o 2 4 (by decide) (by decide) (by decide),
      o 2 5 (by decide) (by decide) (by decide), ?_⟩
    rw [hL.Tx]; exact hL.jg_ne (List.mem_append_right _ (RzD (K := K)).1) (by decide)

/-- `c_m`'s slot is not an entry's `X` or `Y`, nor, for `m ≥ 2`, its `Z`. -/
theorem pre_ne_ent {m : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) {m' : Nat} (h1' : 1 ≤ m') (h16' : m' ≤ 16) :
    K.pre m ≠ K.ent m' 0 ∧ K.pre m ≠ K.ent m' 1 ∧ (2 ≤ m → K.pre m ≠ K.ent m' 2) := by
  rcases Nat.lt_or_ge m 16 with hm | hm
  · rw [pre_eq K h1 (by omega_arith), ent_eq, ent_eq, ent_eq]
    refine ⟨jg_inj hL ?_, jg_inj hL ?_, fun h2 => jg_inj hL ?_⟩ <;> unfold preG <;> split <;> omega_arith
  · obtain rfl : m = 16 := by omega_arith
    rw [pre_16, ent_eq, ent_eq, ent_eq]
    obtain r := List.mem_append_right (jwRo K) (RzD (K := K)).1
    exact ⟨hL.jg_ne r (by omega_arith), hL.jg_ne r (by omega_arith), fun _ => hL.jg_ne r (by omega_arith)⟩

/-- `D`'s slots and `E.x` are not entries' slots. -/
theorem DE_ent {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) :
    K.D.x ≠ K.ent m c ∧ K.D.y ≠ K.ent m c ∧ K.D.z ≠ K.ent m c ∧ K.E.x ≠ K.ent m c := by
  obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
  rw [ent_eq]
  refine ⟨hL.jg_ne (List.mem_append_right _ dx) (by omega_arith), hL.jg_ne (List.mem_append_right _ dy) (by omega_arith),
    hL.jg_ne (List.mem_append_right _ dz) (by omega_arith), ?_⟩
  rw [hL.Tx]; exact jg_inj hL (by omega_arith)

theorem ent_ne {m m' c c' : Nat} (h1 : 1 ≤ m) (h1' : 1 ≤ m') (hc : c < 5) (hc' : c' < 5)
    (h : m ≠ m' ∨ c ≠ c') : K.ent m c ≠ K.ent m' c' := by
  rw [ent_eq, ent_eq]; exact jg_inj hL (by omega_arith)

omit hL in
theorem ent_slots {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) : K.ent m c ∈ jwSlots K := by
  rw [ent_eq]; exact jg_mem (by omega_arith)

omit hL in
theorem ent_ws {m c : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16) (hc : c < 5) : K.ent m c ∈ jwWs K := by
  rw [ent_eq]; exact jg_ws (by omega_arith)

/-- `D`'s slots and `E.x`: written, and distinct. -/
theorem DE_ws : K.D.x ∈ jwWs K ∧ K.D.y ∈ jwWs K ∧ K.D.z ∈ jwWs K ∧ K.E.x ∈ jwWs K := by
  obtain ⟨-, dx, dy, dz⟩ := RzD (K := K)
  exact ⟨other_ws dx, other_ws dy, other_ws dz, by rw [hL.Tx]; exact jg_ws (by decide)⟩

theorem DEJ_ne : K.D.x ≠ K.D.y ∧ K.D.x ≠ K.D.z ∧ K.D.y ≠ K.D.z ∧ K.D.x ≠ K.E.x ∧ K.D.y ≠ K.E.x ∧
    K.D.z ≠ K.E.x := by
  obtain o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
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
  rw [JacWinCfg.prodOps, map_eq_flatMapJ]
  obtain I₀ : PreInvJ K C base size s₀ 0 s₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, fun j h2 h1 => absurd h2 (by omega_arith),
      fun j h2 h1 => absurd h2 (by omega_arith), fun _ _ _ => rfl⟩
  refine fprogB_range_ok (N := 15) (fun i hi t I => ?_) 15 (Nat.le_refl _) s₀ I₀
  rw [fprogB_single]
  -- `Z_{i+2}` is as at `s₀`.
  obtain zS := ent_slots (K := K) (m := i + 2) (c := 2) (by omega_arith) (by omega_arith) (by decide)
  obtain ez : wordsVal t.mem base (K.ent (i + 2) 2) K.M.n = wordsVal s₀.mem base (K.ent (i + 2) 2) K.M.n :=
    I.same _ zS fun j h2 hj e => (pre_ne_ent hL (m := j) (by omega_arith) (by omega_arith) (m' := i + 2) (by omega_arith)
      (by omega_arith)).2.2 h2 e.symm
  obtain ltb : wordsVal t.mem base (K.ent (i + 2) 2) K.M.n < C.p := by
    rw [ez]; exact (hT (i + 2) (by omega_arith) (by omega_arith)).lt 2 (by decide)
  obtain va : wordsVal t.mem base (K.pre (i + 1)) K.M.n < C.p ∧
      tmv C K.M.n base t (K.pre (i + 1)) = cprod (tzJ K C base s₀) (i + 1) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have e : wordsVal t.mem base (K.pre 1) K.M.n = wordsVal s₀.mem base (K.ent 1 2) K.M.n :=
        I.same _ (pre_slots (K := K) (m := 1) (Nat.le_refl _) (by omega_arith)) fun j h2 hj e =>
          absurd (pre_inj hL (Nat.le_refl _) (by omega_arith) (by omega_arith) (by omega_arith) e) (by omega_arith)
      refine ⟨by rw [e]; exact (hT 1 (Nat.le_refl _) (by omega_arith)).lt 2 (by decide), ?_⟩
      rw [tmv_congr e]; rfl
    · exact ⟨I.lt _ (by omega_arith) (by omega_arith), I.val _ (by omega_arith) (by omega_arith)⟩
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod (pre_ws (K := K) (m := i + 2) (by omega_arith) (by omega_arith))
    (pre_slots (K := K) (m := i + 1) (by omega_arith) (by omega_arith)) zS va.1 ltb)
    fun u ⟨su, ku, Uu, Mu, lu, vu, eu⟩ => ?_
  obtain ne : ∀ j, 2 ≤ j → j ≤ i + 1 → K.pre j ≠ K.pre (i + 2) := fun j h2 hj h =>
    absurd (pre_inj hL (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) h) (by omega_arith)
  refine ⟨su, I.keep.trans ku, (I.unch.trans Uu).mono jwW_append, Mu, fun j h2 hj => ?_,
    fun j h2 hj => ?_, fun x hx hne => ?_⟩
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [eu _ (pre_slots (K := K) (by omega_arith) (by omega_arith)) (ne j h2 (by omega_arith))]
      exact I.lt j h2 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      exact lu
  · rcases Nat.lt_or_ge j (i + 2) with hj' | hj'
    · rw [tmv_congr (eu _ (pre_slots (K := K) (by omega_arith) (by omega_arith)) (ne j h2 (by omega_arith)))]
      exact I.val j h2 (by omega_arith)
    · obtain rfl : j = i + 2 := by omega_arith
      rw [vu, va.2, tmv_congr ez]
      rfl
  · rw [eu x hx (hne _ (by omega_arith) (by omega_arith))]
    exact I.same x hx fun j h2 hj => hne j h2 (by omega_arith)

/-! ## Back from entry `16` -/

theorem cprod_ne_zero16 (hC : Law C) {Z : Nat → Fe C} (hZ : ∀ j, 1 ≤ j → j ≤ 16 → Z j ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ 16 → cprod Z m ≠ 0
  | 0, h, _ => absurd h (by omega_arith)
  | 1, _, _ => hZ 1 (Nat.le_refl _) (by omega_arith)
  | j + 2, _, h16 => hC.mul_ne_zero (cprod_ne_zero16 hC hZ (j + 1) (by omega_arith) (by omega_arith)) (hZ _ (by omega_arith) h16)

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
    WP isa (fprogB K.M (K.backOps (16 - i))).inline t (BackInvJ K C base size u₀ X Y Z (i + 1)) := by
  generalize hm : 16 - i = m
  obtain hm2 : 2 ≤ m := by omega_arith
  obtain hm16 : m ≤ 16 := by omega_arith
  obtain hmi : 16 - (i + 1) = m - 1 := by omega_arith
  obtain hm1 : 1 ≤ m := by omega_arith
  obtain hm1' : 1 ≤ m - 1 := by omega_arith
  obtain hm15 : m - 1 ≤ 16 := by omega_arith
  obtain hm15' : m - 1 ≤ 15 := by omega_arith
  obtain ⟨dxy, dxz, dyz, dxe, dye, dze⟩ := DEJ_ne hL
  obtain ⟨Dw, Dyw, Dzw, Ew⟩ := DE_ws hL
  obtain Ds := ws_mem Dw; have Dys := ws_mem Dyw; have Dzs := ws_mem Dzw; have Es := ws_mem Ew
  obtain xw := ent_ws (K := K) (m := m) (c := 0) hm1 hm16 (by decide)
  obtain yw := ent_ws (K := K) (m := m) (c := 1) hm1 hm16 (by decide)
  obtain zS := ent_slots (K := K) (m := m) (c := 2) hm1 hm16 (by decide)
  obtain dm := fun c (hc : c < 5) => DE_ent hL (m := m) (c := c) hm1 hm16 hc
  -- What is not done at `t`.
  obtain nd : ∀ {x}, x ∈ jwSlots K → x ∉ backW K → (∀ j, m < j → j ≤ 16 →
      x ≠ K.ent j 0 ∧ x ≠ K.ent j 1) → wordsVal t.mem base x K.M.n = wordsVal u₀.mem base x K.M.n :=
    fun hx h1 h3 => I.same _ hx h1 fun j hj hj' => h3 j (by omega_using [hj, hm]) hj'
  obtain pc := pre_ne_DE hL (m := m - 1) hm1' hm15
  obtain cS := pre_slots (K := K) (m := m - 1) hm1' hm15
  obtain ec : wordsVal t.mem base (K.pre (m - 1)) K.M.n = wordsVal u₀.mem base (K.pre (m - 1)) K.M.n :=
    nd cS (not_backW pc.1 pc.2.1 pc.2.2.1 pc.2.2.2) fun j hj hj' =>
      ⟨(pre_ne_ent hL hm1' hm15 (m' := j) (by omega_using [hj, hm1]) hj').1,
        (pre_ne_ent hL hm1' hm15 (m' := j) (by omega_using [hj, hm1]) hj').2.1⟩
  obtain notB : ∀ c < 5, K.ent m c ∉ backW K := fun c hc =>
    not_backW (dm c hc).1.symm (dm c hc).2.1.symm (dm c hc).2.2.1.symm (dm c hc).2.2.2.symm
  obtain enem : ∀ c < 5, ∀ j, m < j → j ≤ 16 → K.ent m c ≠ K.ent j 0 ∧ K.ent m c ≠ K.ent j 1 :=
    fun c hc j hj _ => ⟨ent_ne hL hm1 (by omega_using [hj, hm1]) hc (by decide) (Or.inl (by omega_using [hj])),
      ent_ne hL hm1 (by omega_using [hj, hm1]) hc (by decide) (Or.inl (by omega_using [hj]))⟩
  obtain ez : wordsVal t.mem base (K.ent m 2) K.M.n = wordsVal u₀.mem base (K.ent m 2) K.M.n :=
    nd zS (notB 2 (by decide)) (enem 2 (by decide))
  obtain ex0 : wordsVal t.mem base (K.ent m 0) K.M.n = wordsVal u₀.mem base (K.ent m 0) K.M.n :=
    nd (ws_mem xw) (notB 0 (by decide)) (enem 0 (by decide))
  obtain ey0 : wordsVal t.mem base (K.ent m 1) K.M.n = wordsVal u₀.mem base (K.ent m 1) K.M.n :=
    nd (ws_mem yw) (notB 1 (by decide)) (enem 1 (by decide))
  obtain hcm := cprod_succ Z hm2
  obtain nz := cprod_ne_zero16 hC B.nz (m - 1) hm1' hm15
  obtain ⟨tr1, tr2⟩ := trick_step hC nz (B.nz m hm1 hm16)
  rw [← hcm] at tr1 tr2
  rw [JacWinCfg.backOps, fprogB_cons_iff]
  -- `D.x = E.x c_{m-1}`.
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod Dw Es cS I.ex_lt
    (by rw [ec]; exact (B.c _ hm1' hm15').1)) fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  rw [fprogB_cons_iff]
  obtain ex₁ := e₁ _ Es dxe.symm
  -- `E.x = E.x Z_m`.
  refine WP.mono (slotMulJ_ok hL hp s₁ M₁ Ew Es zS (by rw [ex₁]; exact I.ex_lt)
    (by rw [e₁ _ zS (dm 2 (by decide)).1.symm, ez]; exact (B.z m hm1 hm16).1))
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  rw [fprogB_cons_iff]
  obtain dx₂ := e₂ _ Ds dxe
  -- `D.y = D.x²`.
  refine WP.mono (slotMulJ_ok hL hp s₂ M₂ Dyw Ds Ds (by rw [dx₂]; exact l₁) (by rw [dx₂]; exact l₁))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_
  rw [fprogB_cons_iff]
  obtain xx₃ : wordsVal t₃.mem base (K.ent m 0) K.M.n = wordsVal u₀.mem base (K.ent m 0) K.M.n := by
    rw [e₃ _ (ws_mem xw) (dm 0 (by decide)).2.1.symm, e₂ _ (ws_mem xw) (dm 0 (by decide)).2.2.2.symm,
      e₁ _ (ws_mem xw) (dm 0 (by decide)).1.symm, ex0]
  -- `X_m = X_m D.y`.
  refine WP.mono (slotMulJ_ok hL hp s₃ M₃ xw (ws_mem xw) Dys
    (by rw [xx₃]; exact (B.x m hm1 hm16).1) l₃)
    fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  rw [fprogB_cons_iff]
  obtain dy₄ := e₄ _ Dys (dm 0 (by decide)).2.1
  obtain dx₄ : wordsVal t₄.mem base K.D.x K.M.n = wordsVal t₂.mem base K.D.x K.M.n := by
    rw [e₄ _ Ds (dm 0 (by decide)).1, e₃ _ Ds dxy]
  -- `D.z = D.y D.x`.
  refine WP.mono (slotMulJ_ok hL hp s₄ M₄ Dzw Dys Ds (by rw [dy₄]; exact l₃) (by rw [dx₄, dx₂]; exact l₁))
    fun t₅ ⟨s₅, k₅, U₅, M₅, l₅, v₅, e₅⟩ => ?_
  rw [fprogB_single]
  obtain yy₅ : wordsVal t₅.mem base (K.ent m 1) K.M.n = wordsVal u₀.mem base (K.ent m 1) K.M.n := by
    rw [e₅ _ (ws_mem yw) (dm 1 (by decide)).2.2.1.symm,
      e₄ _ (ws_mem yw) (ent_ne hL hm1 hm1 (by decide) (by decide) (Or.inr (by decide))),
      e₃ _ (ws_mem yw) (dm 1 (by decide)).2.1.symm, e₂ _ (ws_mem yw) (dm 1 (by decide)).2.2.2.symm,
      e₁ _ (ws_mem yw) (dm 1 (by decide)).1.symm, ey0]
  -- `Y_m = Y_m D.z`.
  refine WP.mono (slotMulJ_ok hL hp s₅ M₅ yw (ws_mem yw) Dzs
    (by rw [yy₅]; exact (B.y m hm1 hm16).1) l₅)
    fun t₆ ⟨s₆, k₆, U₆, M₆, l₆, v₆, e₆⟩ => ?_
  obtain k6 := fun {x} (hx : x ∈ jwSlots K) (hb : x ∉ backW K) (h0 : x ≠ K.ent m 0) (h1 : x ≠ K.ent m 1) =>
    keep6 (t := t) (m := m) e₁ e₂ e₃ e₄ e₅ e₆ hx hb h0 h1
  obtain vD : tmv C K.M.n base t₁ K.D.x = Z m ^ (C.p - 2) := by
    rw [v₁, I.ex, hm, tmv_congr ec, (B.c _ hm1' hm15').2]; exact tr1
  obtain vE : tmv C K.M.n base t₂ K.E.x = cprod Z (m - 1) ^ (C.p - 2) := by
    rw [v₂, tmv_congr ex₁, I.ex, hm, tmv_congr (e₁ _ zS (dm 2 (by decide)).1.symm), tmv_congr ez,
      (B.z m hm1 hm16).2]; exact tr2
  obtain ex₆ : wordsVal t₆.mem base K.E.x K.M.n = wordsVal t₂.mem base K.E.x K.M.n := by
    rw [e₆ _ Es (dm 1 (by decide)).2.2.2, e₅ _ Es dze.symm, e₄ _ Es (dm 0 (by decide)).2.2.2,
      e₃ _ Es dye.symm]
  obtain xx₆ : wordsVal t₆.mem base (K.ent m 0) K.M.n = wordsVal t₄.mem base (K.ent m 0) K.M.n := by
    rw [e₆ _ (ws_mem xw) (ent_ne hL hm1 hm1 (by decide) (by decide) (Or.inr (by decide))),
      e₅ _ (ws_mem xw) (dm 0 (by decide)).2.2.1.symm]
  obtain vDy : tmv C K.M.n base t₃ K.D.y = Z m ^ (C.p - 2) * Z m ^ (C.p - 2) := by
    rw [v₃, tmv_congr dx₂, vD]
  obtain vDz : tmv C K.M.n base t₅ K.D.z = Z m ^ (C.p - 2) * Z m ^ (C.p - 2) * Z m ^ (C.p - 2) := by
    rw [v₅, tmv_congr dy₄, vDy, tmv_congr dx₄, tmv_congr dx₂, vD]
  refine ⟨s₆, I.keep.trans (k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆))))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆)))))).mono fun w hw => ?_, M₆,
    by rw [ex₆]; exact l₂, by rw [hmi, tmv_congr ex₆, vE], fun j hj hj16 => ?_, fun x hx hb h3 => ?_⟩
  · simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge m j with hj' | hj'
    · have tj := fun c (hc : c < 5) => DE_ent hL (m := j) (c := c) (by omega_using [hj']) hj16 hc
      obtain nb := fun c (hc : c < 5) =>
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

/-- The entries' `X` and `Y` by the square and the cube of their
`Z^(p-2)`, from `c_16^(p-2)` in `E.x`. -/
theorem backJ_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {base : Addr}
    {u₀ : State} {X Y Z : Nat → Fe C} (B : BackStartJ K C base u₀ X Y Z) (hs : Scr u₀ base size)
    (hM : ModOkW K.M size C.p u₀.mem base) (hel : wordsVal u₀.mem base K.E.x K.M.n < C.p)
    (hev : tmv C K.M.n base u₀ K.E.x = cprod Z 16 ^ (C.p - 2)) :
    WP isa (fprogB K.M K.normOps).inline u₀ fun t => Scr t base size ∧
      KeepRegs (clob K.M.n) u₀ t ∧ Unch base (jwW K) u₀.mem t.mem ∧ ModOkW K.M size C.p t.mem base ∧
      ∀ j, 1 ≤ j → j ≤ 16 → DoneJ K C base X Y Z t j := by
  rw [JacWinCfg.normOps, fprogB_append_iff]
  obtain I₀ : BackInvJ K C base size u₀ X Y Z 0 u₀ :=
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, hel, hev, fun j hj hj' => absurd hj' (by omega_arith),
      fun _ _ _ _ => rfl⟩
  refine WP.mono (fprogB_range_ok (N := 15) (fun i hi t I => backJ_step hL hp hC B hi I) 15 (Nat.le_refl _) u₀ I₀)
    fun t I => ?_
  obtain ⟨dxy, dxz, dyz, dxe, dye, dze⟩ := DEJ_ne hL
  obtain ⟨Dw, Dyw, Dzw, Ew⟩ := DE_ws hL
  obtain Ds := ws_mem Dw; have Dys := ws_mem Dyw; have Dzs := ws_mem Dzw; have Es := ws_mem Ew
  obtain xw := ent_ws (K := K) (m := 1) (c := 0) (Nat.le_refl _) (by omega_arith) (by decide)
  obtain yw := ent_ws (K := K) (m := 1) (c := 1) (Nat.le_refl _) (by omega_arith) (by decide)
  obtain d1 := fun c (hc : c < 5) => DE_ent hL (m := 1) (c := c) (Nat.le_refl _) (by omega_arith) hc
  obtain nb := fun c (hc : c < 5) =>
    not_backW (d1 c hc).1.symm (d1 c hc).2.1.symm (d1 c hc).2.2.1.symm (d1 c hc).2.2.2.symm
  obtain ex1 : wordsVal t.mem base (K.ent 1 0) K.M.n = wordsVal u₀.mem base (K.ent 1 0) K.M.n :=
    I.same _ (ws_mem xw) (nb 0 (by decide)) fun j hj _ =>
      ⟨ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith)),
        ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))⟩
  obtain ey1 : wordsVal t.mem base (K.ent 1 1) K.M.n = wordsVal u₀.mem base (K.ent 1 1) K.M.n :=
    I.same _ (ws_mem yw) (nb 1 (by decide)) fun j hj _ =>
      ⟨ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith)),
        ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))⟩
  obtain hex : tmv C K.M.n base t K.E.x = Z 1 ^ (C.p - 2) := by rw [I.ex]; rfl
  rw [fprogB_cons_iff]
  -- `D.y = E.x²`.
  refine WP.mono (slotMulJ_ok hL hp I.scr I.mod Dyw Es Es I.ex_lt I.ex_lt)
    fun t₁ ⟨s₁, k₁, U₁, M₁, l₁, v₁, e₁⟩ => ?_
  rw [fprogB_cons_iff]
  -- `X_1 = X_1 D.y`.
  refine WP.mono (slotMulJ_ok hL hp s₁ M₁ xw (ws_mem xw) Dys
    (by rw [e₁ _ (ws_mem xw) (d1 0 (by decide)).2.1.symm, ex1]; exact (B.x 1 (Nat.le_refl _) (by omega_arith)).1) l₁)
    fun t₂ ⟨s₂, k₂, U₂, M₂, l₂, v₂, e₂⟩ => ?_
  rw [fprogB_cons_iff]
  obtain dy₂ := e₂ _ Dys (d1 0 (by decide)).2.1
  obtain ee₂ : wordsVal t₂.mem base K.E.x K.M.n = wordsVal t.mem base K.E.x K.M.n := by
    rw [e₂ _ Es (d1 0 (by decide)).2.2.2, e₁ _ Es dye.symm]
  -- `D.z = D.y E.x`.
  refine WP.mono (slotMulJ_ok hL hp s₂ M₂ Dzw Dys Es (by rw [dy₂]; exact l₁) (by rw [ee₂]; exact I.ex_lt))
    fun t₃ ⟨s₃, k₃, U₃, M₃, l₃, v₃, e₃⟩ => ?_
  rw [fprogB_single]
  obtain yy₃ : wordsVal t₃.mem base (K.ent 1 1) K.M.n = wordsVal t.mem base (K.ent 1 1) K.M.n := by
    rw [e₃ _ (ws_mem yw) (d1 1 (by decide)).2.2.1.symm,
      e₂ _ (ws_mem yw) (ent_ne hL (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide) (Or.inr (by decide))),
      e₁ _ (ws_mem yw) (d1 1 (by decide)).2.1.symm]
  -- `Y_1 = Y_1 D.z`.
  refine WP.mono (slotMulJ_ok hL hp s₃ M₃ yw (ws_mem yw) Dzs
    (by rw [yy₃, ey1]; exact (B.y 1 (Nat.le_refl _) (by omega_arith)).1) l₃)
    fun t₄ ⟨s₄, k₄, U₄, M₄, l₄, v₄, e₄⟩ => ?_
  obtain k4 : ∀ x ∈ jwSlots K, x ∉ backW K → x ≠ K.ent 1 0 → x ≠ K.ent 1 1 →
      wordsVal t₄.mem base x K.M.n = wordsVal t.mem base x K.M.n := fun x hx hb h0 h1 => by
    simp only [backW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [e₄ x hx h1, e₃ x hx hb.2.2.1, e₂ x hx h0, e₁ x hx hb.2.1]
  refine ⟨s₄, I.keep.trans (k₁.trans (k₂.trans (k₃.trans k₄))),
    (I.unch.trans (U₁.trans (U₂.trans (U₃.trans U₄)))).mono fun w hw => ?_, M₄, fun j hj hj16 => ?_⟩
  · simp only [List.mem_append] at hw; rcases hw with hw | hw | hw | hw | hw <;> exact hw
  · rcases Nat.lt_or_ge 1 j with hj' | hj'
    · have tj := fun c (hc : c < 5) => DE_ent hL (m := j) (c := c) (by omega_arith) hj16 hc
      obtain nbj := fun c (hc : c < 5) =>
        not_backW (tj c hc).1.symm (tj c hc).2.1.symm (tj c hc).2.2.1.symm (tj c hc).2.2.2.symm
      exact (I.done j (by omega_arith) hj16).congr
        (k4 _ (ent_slots (K := K) (by omega_arith) hj16 (by decide)) (nbj 0 (by decide))
          (ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith)))
          (ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))))
        (k4 _ (ent_slots (K := K) (by omega_arith) hj16 (by decide)) (nbj 1 (by decide))
          (ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith)))
          (ent_ne hL (by omega_arith) (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))))
    · obtain rfl : j = 1 := by omega_arith
      obtain xx₄ : wordsVal t₄.mem base (K.ent 1 0) K.M.n = wordsVal t₂.mem base (K.ent 1 0) K.M.n := by
        rw [e₄ _ (ws_mem xw) (ent_ne hL (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide)
          (Or.inr (by decide))), e₃ _ (ws_mem xw) (d1 0 (by decide)).2.2.1.symm]
      refine ⟨by rw [xx₄]; exact l₂, l₄, ?_, ?_⟩
      · rw [tmv_congr xx₄, v₂, tmv_congr (e₁ _ (ws_mem xw) (d1 0 (by decide)).2.1.symm), tmv_congr ex1,
          (B.x 1 (Nat.le_refl _) (by omega_arith)).2, v₁, hex]
      · rw [v₄, tmv_congr yy₃, tmv_congr ey1, (B.y 1 (Nat.le_refl _) (by omega_arith)).2, v₃, tmv_congr dy₂, v₁,
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
    ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, fun j h0 => absurd h0 (by omega_arith), fun _ _ _ => rfl⟩
  obtain zs := ent_slots (K := K) (m := i / 3 + 1) (c := 2 + i % 3) (by omega_arith) (by omega_arith) (by omega_arith)
  obtain zw := ent_ws (K := K) (m := i / 3 + 1) (c := 2 + i % 3) (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (setConst_ok st (n := K.M.n) (o := K.ent (i / 3 + 1) (2 + i % 3)) (hL.lay.le _ zs) hx)
    fun u ⟨eu, ku, Ou⟩ => ?_
  have hn := st.nowrap
  obtain same : ∀ y ∈ jwSlots K, y ≠ K.ent (i / 3 + 1) (2 + i % 3) →
      wordsVal u.mem base y K.M.n = wordsVal t.mem base y K.M.n := fun y hy hne =>
    Ou.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact hL.lay.apart y _ hy zs hne) (by have := hL.lay.le y hy; omega_arith)
  refine ⟨st.of_keepRegs ku (by decide), kt.trans ku, (Ut.trans Ou.unch).mono fun w hw => ?_,
    fun j hj => ?_, fun y hy hne => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · rw [List.mem_singleton.mp hw]; exact mem_jwW_ws zw
  · rcases Nat.lt_or_ge j i with hj' | hj'
    · rw [same _ (ent_slots (K := K) (by omega_arith) (by omega_arith) (by omega_arith))
        (ent_ne hL (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact vt j hj'
    · obtain rfl : j = i := by omega_arith
      exact eu
  · rw [same y hy (hne _ (by omega_arith))]
    exact et y hy fun j hj => hne j (by omega_arith)

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
    · exact h x hx) (by have := hL.lay.le x hx; omega_arith)

theorem InvSpecJ.mo {inv : Prog isa} {base : Addr} {IW : List (Nat × Nat)}
    (h : InvSpecJ K C base size inv IW) (hL : JacWinLay K size) {mem : Mem}
    (hM : ModOkW K.M size C.p mem base) : ∀ w ∈ IW, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  rcases h.w w hw with rfl | rfl | ⟨h, -⟩
  · have := hL.lay.mo K.E.x (by rw [hL.Tx]; exact jg_mem (by decide)); dsimp only; omega_arith
  · have := hM.sep; dsimp only; omega_arith
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
  obtain hsu := I.scr.of_keepRegs Ku (rdi_not_invClob' _)
  obtain Mu := I.mod.unch Uu (hI.mo hL I.mod) hn
  -- The table and the products at `u₀`.
  obtain tsame : ∀ {m c}, 1 ≤ m → m ≤ 16 → c < 3 → wordsVal u₀.mem base (K.ent m c) K.M.n =
      wordsVal s.mem base (K.ent m c) K.M.n := @fun m c h1 h16 hc => by
    obtain ys := ent_slots (K := K) h1 h16 (show c < 5 by omega_arith)
    rw [hI.same hL Uu hn ys (DE_ent hL h1 h16 (show c < 5 by omega_arith)).2.2.2.symm]
    refine I.same _ ys fun j h2 hj e => ?_
    obtain pe := pre_ne_ent hL (m := j) (by omega_arith) (by omega_arith) (m' := m) h1 h16
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_arith) with rfl | rfl | rfl
    · exact pe.1 e.symm
    · exact pe.2.1 e.symm
    · exact pe.2.2 h2 e.symm
  obtain B : BackStartJ K C base u₀ (fun j => tmv C K.M.n base s (K.ent j 0))
      (fun j => tmv C K.M.n base s (K.ent j 1)) (tzJ K C base s) := by
    refine ⟨fun j h1 h15 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_, fun j h1 h16 => ?_⟩
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · obtain rfl : j = 1 := by omega_arith
        obtain e := tsame (m := 1) (c := 2) (Nat.le_refl _) (by omega_arith) (by decide)
        have pe : K.pre 1 = K.ent 1 2 := rfl
        rw [pe, e, tmv_congr e]
        exact ⟨(hT 1 (Nat.le_refl _) (by omega_arith)).lt 2 (by decide), rfl⟩
      · have e := hI.same hL Uu hn (pre_slots (K := K) (by omega_arith) (by omega_arith))
          (pre_ne_DE hL (m := j) (by omega_arith) (by omega_arith)).2.2.2
        rw [e, tmv_congr e]
        exact ⟨I.lt j hj (by omega_arith), I.val j hj (by omega_arith)⟩
    · have e := tsame (c := 0) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 0 (by decide), rfl⟩
    · have e := tsame (c := 1) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 1 (by decide), rfl⟩
    · have e := tsame (c := 2) h1 h16 (by decide)
      rw [e, tmv_congr e]; exact ⟨(hT j h1 h16).lt 2 (by decide), rfl⟩
    · exact (hT j h1 h16).z
  obtain hev : tmv C K.M.n base u₀ K.E.x = cprod (tzJ K C base s) 16 ^ (C.p - 2) := by
    rw [vu]; exact congrArg (· ^ (C.p - 2)) (I.val 16 (by decide) (Nat.le_refl _))
  refine WP.seq (WP.mono (backJ_ok hL hp hC B hsu Mu lu hev) fun v ⟨sv, kv, Uv, Mv, dv⟩ => ?_)
  refine WP.mono (onesJ_ok hL (x := K.one) (Nat.lt_trans hone_lt hpn) 48 (Nat.le_refl _) v sv)
    fun w ⟨sw, kw, Uw, ow, ew⟩ => ?_
  obtain c1 : ∀ r ∈ [Reg.rax], r ∈ invClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [invClob, powClob, clob]
  obtain c2 : ∀ r ∈ clob K.M.n, r ∈ invClob K.M.n := fun r h =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  obtain U : Unch base (jwW K ++ IW) s.mem w.mem :=
    (I.unch.trans (Uu.trans (Uv.trans Uw))).mono fun x hx => by
      simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx | hx | hx <;> simp [hx]
  -- `Z`, `Z²`, `Z³` one.
  obtain one3 : ∀ m, 1 ≤ m → m ≤ 16 → ∀ c, 2 ≤ c → c < 5 → wordsVal w.mem base (K.ent m c) K.M.n = K.one :=
    fun m h1 h16 c h2 h5 => by
      obtain e := ow (3 * (m - 1) + (c - 2)) (by omega_arith)
      rwa [show (3 * (m - 1) + (c - 2)) / 3 + 1 = m by omega_arith,
        show 2 + (3 * (m - 1) + (c - 2)) % 3 = c by omega_arith] at e
  obtain xy : ∀ m, 1 ≤ m → m ≤ 16 → ∀ c < 2, wordsVal w.mem base (K.ent m c) K.M.n =
      wordsVal v.mem base (K.ent m c) K.M.n := fun m h1 h16 c hc =>
    ew _ (ent_slots (K := K) h1 h16 (by omega_arith)) fun j hj =>
      ent_ne hL h1 (by omega_arith) (by omega_arith) (by omega_arith) (Or.inr (by omega_arith))
  refine ⟨sw, ((I.keep.mono c2).trans Ku).trans ((kv.mono c2).trans (kw.mono c1)), U,
    Mv.unch Uw (hL.w_mo Mv) hn, fun m h1 h16 => ?_, fun m h1 h16 => one3 m h1 h16 2 (by decide) (by decide)⟩
  obtain ⟨l0, l1, v0, v1⟩ := dv m h1 h16
  obtain ex := xy m h1 h16 0 (by decide)
  obtain ey := xy m h1 h16 1 (by decide)
  obtain to1 : ∀ c, 2 ≤ c → c < 5 → tmv C K.M.n base w (K.ent m c) = 1 := fun c h2 h5 => by
    show toM _ _ _ = 1; rw [one3 m h1 h16 c h2 h5]; exact hone
  obtain J : InvJ C (tmv C K.M.n base s (K.ent m 0)) (tmv C K.M.n base s (K.ent m 1))
      (tmv C K.M.n base s (entS K m 2)) (mul m P) := (hT m h1 h16).jac
  obtain Z0 := (hT m h1 h16).z
  dsimp only at v0 v1
  generalize hz : tmv C K.M.n base s (entS K m 2) = Z at J Z0
  have hz' : tzJ K C base s m = Z := hz
  rw [hz'] at v0 v1
  obtain hf := hC.fermat Z0
  generalize Z ^ (C.p - 2) = zi at v0 v1 hf
  obtain zi0 : zi ≠ 0 := fun h => h1p (by rw [← hf, h, Fin.mul_zero])
  refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
  · rcases (show c = 0 ∨ c = 1 ∨ (2 ≤ c ∧ c < 5) by omega_arith) with rfl | rfl | ⟨h2, h5⟩
    · show wordsVal _ base (K.ent m 0) _ < _; rw [ex]; exact l0
    · show wordsVal _ base (K.ent m 1) _ < _; rw [ey]; exact l1
    · show wordsVal _ base (K.ent m c) _ < _; rw [one3 m h1 h16 c h2 h5]; exact hone_lt
  · show InvJ C (tmv C K.M.n base w (K.ent m 0)) (tmv C K.M.n base w (K.ent m 1))
      (tmv C K.M.n base w (K.ent m 2)) _
    rw [tmv_congr ex, tmv_congr ey, v0, v1, to1 2 (by decide) (by decide)]
    exact J.rescale hC zi0 h1p (by simp only [Fin.mul_one]) (by simp only [Fin.mul_one]) (by rw [Fin.mul_one, hf])
  · show tmv C K.M.n base w (K.ent m 2) ≠ 0
    rw [to1 2 (by decide) (by decide)]; exact h1p
  · show tmv C K.M.n base w (K.ent m 3) = tmv C K.M.n base w (K.ent m 2) * tmv C K.M.n base w (K.ent m 2)
    rw [to1 3 (by decide) (by decide), to1 2 (by decide) (by decide), Fin.mul_one]
  · show tmv C K.M.n base w (K.ent m 4) = tmv C K.M.n base w (K.ent m 3) * tmv C K.M.n base w (K.ent m 2)
    rw [to1 4 (by decide) (by decide), to1 3 (by decide) (by decide), to1 2 (by decide) (by decide), Fin.mul_one]

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.WinJacEntryA`, which only this module used -/

section

/-!
# 5-bit windows with an affine table on x86-64: the entry of a digit

`JacWinCfg.selectA` selects only the entry's `X` and `Y`, the first `16 n`
bytes of the entry, by `selPassAt_ok` or `selPassYSt_ok` (`jselectA_ok`),
and sets `T`'s `Z` to one, which every entry's is once the table is affine
(`JTblOne`). With `negY`, `T` then holds digit `j`'s point with `Z = 1`
(`jentryA_ok`): what the mixed addition reads.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The selection of an iteration: `T`'s `X` and `Y` are entry `a`'s, or
zero for `a = 0`, and its `Z` is one. -/
theorem jselectA_ok (hL : JacWinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 16)
    (hone : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block K.selectA) s fun t =>
      (∀ c < 2, wordsVal t.mem base (jg K (80 + c)) K.M.n =
        if 1 ≤ a then wordsVal s.mem base (jg K (5 * (a - 1) + c)) K.M.n else 0) ∧
      wordsVal t.mem base (jg K 82) K.M.n = K.one ∧
      KeepRegs [.rax, .rcx, .rdx] s t ∧ Outside base (jg K 80) (40 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  have hg := hL.grid_le
  have ht := hL.tbl31
  have h6 := hL.n6
  obtain h4 : 4 ≤ K.M.n := by rcases hL.n46 with h | h <;> omega_using [h]
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
  rw [JacWinCfg.selectA, List.append_assoc, WP.block_append_iff]
  -- `rdx = rdi + tbl`.
  refine WP.mono (show WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]) s
      (fun s₁ => s₁.gpr .rdx = base + BitVec.ofNat 64 K.tbl ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.map_some, imm32_sext ht, hs.rdi, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨x₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hT : K.T = jg K 80 := hL.T80
  obtain hTl : K.T + 40 * K.M.n ≤ size := by rw [hT]; unfold jg; omega_using [hg]
  have hTt : K.T = K.tbl + 16 * K.st := hL.T
  obtain hr : ∀ e < 16, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (K.st * e + 16 * c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := Nat.mul_le_mul_left K.st (show e + 1 ≤ 16 by omega_using [he])
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega_using [hTl, hTt, hc, this]) (by decide)⟩
  -- The pass: the first `n` pieces of the entry.
  obtain hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st ((K.M.n + 1) / 2) (qY K.M.n)
      else selPassAt K.T 16 K.st K.M.n (16 * ·))) s₁ fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.T + 16 * c)) 128 =
        accVal s₁.mem (base + BitVec.ofNat 64 K.tbl) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.M.n) s₁.mem t.mem ∧ KeepRegs [.rcx] s₁ t := by
    split
    · exact selPassYSt_ok hs₁ (by omega_using [hnp, h2n]) (by omega_using [hnp, h2n]) (by decide) (by omega_using [ha]) (by omega_using [hst, h2n]) (by omega_using [hnp, hst]) h8₁ x₁
        ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (d := K.tbl) (by omega_using [hTl, hTt]) (by omega_using [hnp, hst])⟩
        (by omega_using [hTl])
    · exact (selPassAt_ok (d := 0) hs₁ (by omega_using [hnp, h2n]) (by decide) (by omega_using [ha]) h8₁ x₁ (fun c _ => by omega_using [])
        hr (by omega_using [hTl])).mono
        fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => by rw [← a₂ c hc, Nat.add_zero], by rw [← Nat.add_zero K.T]; exact O₂, k₂⟩
  rw [WP.block_append_iff]
  refine WP.mono hpass fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hEz : K.E.z = K.T + 16 * K.M.n := rfl
  refine WP.mono (setConst_ok hs₂ (o := K.E.z) (by rw [hEz]; omega_using [hTl]) hone) fun t ⟨e₃, k₃, O₃⟩ =>
    ⟨fun c hc => ?_, by rw [← hL.Tz]; exact e₃, ?_, ?_⟩
  · have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 2 by omega_using [hc])
    rw [Nat.mul_succ] at hcn
    obtain eT : jg K (80 + c) = K.T + 8 * (K.M.n * c) := by
      rw [hT]; unfold jg; rw [Nat.mul_add, ← Nat.mul_assoc]; omega_using []
    rw [eT, O₃.wordsVal (by rw [hEz]; omega_using [hcn]) (by omega_using [ht, hnp, hst, h2n, hTt, hcn])]
    obtain hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    obtain hw : ∀ i < K.M.n, word s₂.mem base (K.T + 8 * (K.M.n * c) + 8 * i) =
        if 1 ≤ a then word s.mem base (jg K (5 * (a - 1) + c) + 8 * i) else 0 := by
      intro i hi
      obtain ⟨c', q, hq, e⟩ : ∃ c' q, q < 2 ∧ K.M.n * c + i = 2 * c' + q :=
        ⟨(K.M.n * c + i) / 2, (K.M.n * c + i) % 2, Nat.mod_lt _ (by decide), by omega_using []⟩
      obtain hc' : c' < K.M.n := by omega_using [hcn, hi, e]
      obtain w := accVal_word1 (a₂ c' hc') hq
      rw [show K.T + 16 * c' + 8 * q = K.T + 8 * (K.M.n * c) + 8 * i by omega_using [e]] at w
      rw [w]
      by_cases h1 : 1 ≤ a
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1), hX]
        congr 1; unfold jg JacWinCfg.st
        rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
          rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
          Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c, Nat.mul_assoc 8 K.M.n (5 * (a - 1))]
        omega_using [e]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1])), ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine wordsVal_congr₂ _ _ _ fun i hi => ?_
      rw [hw i hi, ite_eq_left_of_eq_true _ _ (eq_true h1)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine wordsVal_zeros fun i hi => ?_
      rw [hw i hi, ite_eq_right_of_eq_false _ _ (eq_false h1)]
  · refine ⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.2.2.1], by rw [k₃.wr, k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₃.gpr r (by simp [hr.1]), k₂.gpr r (by simp [hr.2.1]), k₁.1 r (by simp [hr.2.2])]
  · rw [← hT, ← k₁.2.1]
    exact (O₂.mono (Nat.le_refl _) (by omega_using [])).trans (O₃.mono (by rw [hEz]; omega_using []) (by rw [hEz]; omega_using []))

/-- What `T` holds after an iteration's selection and the negation, from `s`:
`Z` one, and digit `j`'s point for a nonzero digit. -/
structure JEntA (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k' j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  lt : ∀ c < 3, wordsVal t.mem base (TS K c) K.M.n < C.p
  one : wordsVal t.mem base (TS K 2) K.M.n = K.one
  ent : 1 ≤ magH 16 (Window5.nib k' j) → InvJ C (tmv C K.M.n base t (TS K 0)) (tmv C K.M.n base t (TS K 1))
    (tmv C K.M.n base t (TS K 2)) (Window5.winPt C P k' j)

/-- Digit `j`'s affine entry into `T`, negated for a negative digit. -/
theorem jentryA_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) (hO : JTblOne K base s)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.tc.digit ++ K.selectA)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEntA K C base size P s₀ (k + JacWinCfg.offset K.J) j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  obtain hbits := hf.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits
  obtain hwj : 5 * j + 5 ≤ 5 * K.J := by omega_using [hj]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 9; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  have hH : K.tc.H = 16 := rfl
  rw [hwin, hH] at r₁
  generalize ha : magH 16 (Window5.nib k' j) = a at r₁
  obtain ha16 : a ≤ 16 := by rw [← ha]; exact magH_le (by have := Window5.nib_lt k' j; omega_using [this])
  refine WP.mono (jselectA_ok hL hs₁ r₁ ha16 (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨e₂, o₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  obtain U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  obtain F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  -- The negation.
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  obtain hneg : K.neg ∈ jwSlots K := by jw_mem
  obtain hzero : K.zero ∈ jwSlots K := by jw_mem
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  obtain hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [← ty, e₂ 1 (by decide)]
    split
    · exact (hT a (by omega_arith) ha16).lt 1 (by decide)
    · exact hp0
  obtain hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      obtain hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_using [ht, this]) (by omega_using [hn, hbl, ht])]
    have := F₂.bits hL hF t ht; rw [hk'] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) (by rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide),
      k₁.1 _ (by decide), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_using [hyneg])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_using [hn, this]
  -- `T`'s words: as at `s₂` but `Y`.
  obtain keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    obtain hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_using [h1])
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_using [hc]))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_using [hc])).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_using [hc]))) (b64 _ (jg_mem (by omega_using [hc])))]
  obtain y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  obtain keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  obtain tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  obtain hU : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem s₅.mem := by
    rw [← m₁]
    refine (((outside_grid5 (b := 80) O₂).trans k₃.unch).trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h, hL.Ty]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  obtain hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  obtain kk : KeepRegs (clob K.M.n) s s₅ :=
    ((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h])))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  obtain z₅ : wordsVal s₅.mem base (TS K 2) K.M.n = K.one := by rw [keepT 2 (by decide) (by decide)]; exact o₂
  refine ⟨hf.next hL hs₅ (kk.mono clob_powClob) hU (fun w hw => jwLoopW_sub K w (jent_loopW K w hw)), hU,
    kk, fun c hc => ?_, z₅, fun h => ?_⟩
  · by_cases h1 : c = 1
    · subst h1; rw [keepY]; split
      · exact Nat.mod_lt _ hp0
      · exact hy₂
    · by_cases h2 : c = 2
      · subst h2; rw [z₅]; exact hone_lt
      · have hc0 : c = 0 := by omega_using [hc, h1, h2]
        subst hc0
        rw [keepT 0 (by decide) (by decide), e₂ 0 (by decide)]; split
        · exact (hT a ‹_› ha16).lt 0 (by decide)
        · exact hp0
  · rw [ha] at h
    obtain J₂ := (hT a h ha16).jac
    obtain ez : tmv C K.M.n base s₅ (TS K 2) = tmv C K.M.n base s (entS K a 2) := by
      show toM _ _ _ = toM _ _ _; rw [z₅, hO a h ha16]
    obtain ex : tmv C K.M.n base s₅ (TS K 0) = tmv C K.M.n base s (entS K a 0) := by
      show toM _ _ _ = toM _ _ _
      rw [keepT 0 (by decide) (by decide), e₂ 0 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    obtain ey : wordsVal s₂.mem base K.E.y K.M.n = wordsVal s.mem base (entS K a 1) K.M.n := by
      rw [← ty, e₂ 1 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    rw [Window5.winPt_mag, ha, ex, ez]
    by_cases hng : Window5.nib k' j < 16
    · simp only [decide_eq_true hng, ↓reduceIte]
      simp only [decide_eq_true hng, ↓reduceIte] at keepY
      obtain hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = -toM _ _ _
        rw [keepY, toM_sub (by omega_using [hy₂]), toM_zero, ey]
        grind
      rw [hy]; exact J₂.negY
    · simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
      obtain hy : tmv C K.M.n base s₅ (TS K 1) = tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = toM _ _ _; rw [keepY, ey]
      rw [hy]; exact J₂

end VG.Proof.Weierstrass.X86_64

end

end


/-!
# 5-bit windows with an affine table on x86-64

`JacWinCfg.windowA` (`Impl/Weierstrass/X86_64/WinJacA.lean`) leaves `R`
representing `[k]P` in projective coordinates: the table by
`jbuild_ok`, made affine by `normA_ok` (every entry's `Z` one, `JTblOne`),
then the first digit by `jfirst_ok` and the iterations by `jstepA_ok`, which
selects the entry's `X` and `Y` (`jentryA_ok`) and adds it by the mixed addition (`madd_ok`, `jstepA_pt`): right
unless `R = T` (excluded for `k < n` by `Window5.loop_noexc`, as the Jacobian
addition's exceptions) or `R = O` (where `T` is kept, as before).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The mixed addition -/

/-- `D = R + T` by the mixed addition, `T` affine (its `Z` not read). -/
theorem madd_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y], x ∈ V) :
    WP isa (.block (fprog K.M (maddJ K.S K.R K.E K.D))) s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' t ∧
        (E' K.D.x, E' K.D.y, E' K.D.z) = maddJF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) := by
  have hA := hL.addApart
  obtain hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tx, hL.Ty, hL.Tz] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  obtain hR : readsOk (maddJ K.S K.R K.E K.D) V = true := by
    rw [maddJ_eq]
    refine readsOk_mono (readsOk_rename (rcbσ K.S K.R K.E K.D)
      (show readsOk maddJN [11, 12, 13, 14, 15] = true by decide)) fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h <;> rw [h] <;> simp [rcbσ, rcbW, rcbR]
  rw [maddJ_eq] at hR ⊢
  refine WP.mono (fprog_ok hL.lay hp _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun t ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, _, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx
  · exact (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 7) (ofN_run maddJN_ok hA E 8))).trans (maddJN_run _)

/-! ## The point -/

/-- An iteration's result with the mixed addition: `R` for a zero digit, else
`T` where `R = O`, else the mixed sum, a triple of a point of the curve,
`[winE k' J i]P` for `k < n`. -/
theorem jstepA_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 = 1) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (maddJF X1 Y1 Z1 X2 Y2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (maddJF X1 Y1 Z1 X2 Y2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (maddJF X1 Y1 Z1 X2 Y2).2.2) Q := by
  obtain hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  obtain noexc : k < C.n → 1 ≤ Window5.winE (k + 16 * Window5.geom J) J (i + 1) →
      mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P ≠
        Window5.winPt C P (k + 16 * Window5.geom J) i := fun hk he =>
    (Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he).1
  generalize k + 16 * Window5.geom J = k' at hadd h2 hQ1e noexc ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd hQ1e noexc
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    refine ⟨Q1, hQ1, fun hk => ?_, h1⟩
    rw [hQ1e hk, ← hadd, Window5.winPt_zero h0, add_infinity]
  simp only [h0, ↓reduceIte]
  obtain ⟨J2, z2⟩ := h2 (by omega_arith)
  subst z2
  obtain hW := Window5.onCurve_winPt hC hP k' i
  generalize hWe : Window5.winPt C P k' i = W at J2 hW hadd noexc ⊢
  cases W with
  | infinity => exact absurd ((J2.z_zero_iff hC).mpr rfl) hC.one_ne_zero
  | affine x2 y2 =>
  obtain ⟨ex2, ey2⟩ := J2.affine_coords hC
  obtain ex2' : X2 = x2 := by rw [ex2]; grind
  obtain ey2' : Y2 = y2 := by rw [ey2]; grind
  subst ex2' ey2'
  by_cases hz : Z1 = 0
  · simp only [hz, ↓reduceIte]
    refine ⟨_, hW, fun hk => ?_, J2⟩
    rw [← hadd, ← hQ1e hk, (h1.z_zero_iff hC).mp hz, infinity_add']
  simp only [hz, ↓reduceIte]
  by_cases hQW : Q1 = .affine X2 Y2
  · have hZ : (maddJF X1 Y1 Z1 X2 Y2).2.2 = 0 := by
      rw [hQW] at h1
      obtain ⟨hx1, -⟩ := h1.affine_coords hC
      rw [maddJF_z, hx1]; grind
    refine ⟨.infinity, rfl, fun hk => ?_, Or.inl ⟨rfl, hZ⟩⟩
    obtain he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exact absurd ((h1.z_zero_iff hC).mpr (by rw [hQ1e hk, Nat.mul_zero, Window5.mul_zero_pt])) hz
      · exact h
    exact absurd (by rw [← hQ1e hk]; exact hQW) (noexc hk he1)
  · refine ⟨_, hC.onCurve_add hQ1 hW, fun hk => by rw [← hadd, hQ1e hk], ?_⟩
    exact h1.madd hC hM3 hQ1 hW hz hQW

/-! ## An iteration -/

/-- The loop's invariant: `JInv`, with the table's `Z` one. -/
def JInvA (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s : State) : Prop :=
  JInv K C base size P s₀ k j s ∧ JTblOne K base s

theorem JTblOne.loopW (hL : JacWinLay K size) {base : Addr} {s s' : State} (h : JTblOne K base s)
    (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) : JTblOne K base s' :=
  fun m h1 h16 => by
    rw [jgWord_unch hL hU hn (by omega_arith) (loopW_apart hL (by omega_arith))]
    exact h m h1 h16

/-- An iteration, `1 ≤ j ≤ J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstepA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j ≤ K.J) {s : State} (hI : JInvA K C base size P s₀ k j s) :
    WP isa (K.stepA dbl).inline s fun s' => JInvA K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨hI, hO1⟩ := hI
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  rw [JacWinCfg.stepA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain R₁ := R₀.rbxKeeps hL k₁
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  obtain O₂ : JTblOne K base s₂ := (show JTblOne K base s₁ from fun m h1 h16 => by
    rw [m₁]; exact hO1 m h1 h16).loopW hL U₂ hn
  refine WP.seq (WP.mono (jentryA_ok hL hF hpn hone_lt (j := j - 1) (by omega_arith) R₂.fr R₂.tbl O₂ b₂) fun s₃ h₃ =>
    WP.seq (WP.mono h₃ fun s₄ E₄ => ?_))
  -- `R` is not written by the entry.
  obtain hRe : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    obtain hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    refine E₄.unch.wordsVal (fun w hw => ?_) (by have := hL.le (other_mem hxo); omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.lay.tmp x (other_mem hxo)
  obtain U₄ : Unch base (jwLoopW K) s₂.mem s₄.mem := E₄.unch.mono (jent_loopW K)
  -- `T`'s `Z` is one.
  obtain tz1 : 1 ≤ magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1)) →
      tmv C K.M.n base s₄ K.E.z = 1 := fun _ => by
    show toM _ _ _ = 1
    rw [← tz, E₄.one, hone]
  -- `D = R + T`.
  obtain V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.lt 1 (by decide)⟩
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y]
      (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (madd_ok hL hp I₄ (fun x hx => hx)) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  obtain F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  obtain hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  -- `R` and `T` survive the addition.
  obtain keep₅ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n := by
    intro x hx
    obtain hxs : x ∈ jwSlots K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · jw_mem
      · jw_mem
      · jw_mem
      · exact mx
      · exact my
      · exact mz
    refine (ProgKeep.unch k₅).wordsVal (fun w hw => ?_) (by have := hL.le hxs; omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      exact cadd_apart hL x hx y hy
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp x hxs
  refine WP.mono (jmask_ok hL hF (i := j - 1) (by omega_arith) F₅ hb₅) fun s₆ ⟨F₆, U₆, b₆, z₆, w₆⟩ => ?_
  rw [offset_eq] at w₆
  have ent := E₄.ent
  rw [offset_eq] at ent tz1
  obtain R5 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base x K.M.n :=
    fun x hx => by
      rw [keep₅ x (List.mem_append_left [K.E.x, K.E.y, K.E.z] hx), hRe x hx]
  obtain T5 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n :=
    fun x hx => keep₅ x (List.mem_append_right [K.R.x, K.R.y, K.R.z] hx)
  obtain hz : wordsVal s₅.mem base K.R.z K.M.n = 0 ↔ tmv C K.M.n base s₂ K.R.z = 0 := by
    rw [R5 _ (by simp)]; exact (toM_eq_zero_iff hp (R₂.lt _ (by simp))).symm
  obtain Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base s₅ x = E₅ x ∧
      wordsVal s₅.mem base x K.M.n < C.p := fun x hx =>
    ⟨I₅.val x (List.mem_append_left _ hx), I₅.lt x (List.mem_append_left _ hx)⟩
  obtain tvR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₂ x := fun x hx => by rw [R5 x hx]
  obtain tvT : ∀ x ∈ [K.E.x, K.E.y, K.E.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₄ x := fun x hx => by rw [T5 x hx]
  obtain tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  obtain ex : tmv C K.M.n base s₆ K.R.x =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.x
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.x else E₅ K.D.x := by
    obtain w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.x (by simp)) (tvT K.E.x (by simp)) (Dv K.D.x (by simp)).1
  obtain ey : tmv C K.M.n base s₆ K.R.y =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.y
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.y else E₅ K.D.y := by
    obtain w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.y (by simp)) (tvT K.E.y (by simp)) (Dv K.D.y (by simp)).1
  obtain ez : tmv C K.M.n base s₆ K.R.z =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.z
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.z else E₅ K.D.z := by
    obtain w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.z (by simp)) (tvT K.E.z (by simp)) (Dv K.D.z (by simp)).1
  obtain vx := congrArg Prod.fst v₅
  obtain vy := congrArg (fun p => p.2.1) v₅
  obtain vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  rw [vx] at ex; rw [vy] at ey; rw [vz] at ez
  obtain hR := jstepA_pt hC hM3 hO hP hP0 hn17 hn64 (k := k) (i := j - 1) (J := K.J) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (fun h => by
      obtain j1 := ent h
      rw [tx, ty, tz] at j1
      exact ⟨j1, tz1 h⟩)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  obtain U₂₆ : Unch base (jwLoopW K) s₂.mem s₆.mem :=
    ((U₄.trans U₅).trans U₆).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with (hw | hw) | hw <;> exact hw
  refine ⟨⟨⟨⟨Q', hQ', hQe', F₆, ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL U₆ hn
    (by decide), fun x hx => ?_, ?_⟩, b₆⟩, O₂.loopW hL U₂₆ hn⟩, z₆⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp), ← tz]; exact E₄.lt 2 (by decide)
        · exact (Dv _ (by simp)).2
  · rw [ex, ey, ez]
    exact hR

/-! ## The window method -/

/-- What the method reads at the start survives what the table's building
and normalization write. -/
theorem JacWinFixed.unchA (hL : JacWinLay K size) {base : Addr} {s s' : State} {P : Point C} {k : Nat}
    {inv : Prog isa} {IW : List (Nat × Nat)} (hI : InvSpecJ K C base size inv IW)
    (hF : JacWinFixed K C base s P k) (hU : Unch base (jwW K ++ IW) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : JacWinFixed K C base s' P k := by
  obtain ro : ∀ x ∈ jwRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · rw [hL.Tx]; exact hL.jg_apart (List.mem_append_left _ hx) (by decide)
        · exact hL.lay.tmp x (ro_mem hx)
        · exact h x (ro_mem hx)) (by have := hL.le (ro_mem hx); omega_arith)
  obtain tv : ∀ x ∈ jwRo K, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => tmv_congr (ro x hx)
  refine ⟨⟨by rw [ro _ (by jw_mem)]; exact hF.zero, fun x hx => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · have hx' : x ∈ jwRo K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jw_mem
    rw [ro x hx']; exact hF.ro_lt x hx
  · rw [tv _ (by jw_mem), tv _ (by jw_mem), tv _ (by jw_mem)]; exact hF.pt
  · rw [tv _ (by jw_mem)]; exact hF.pz
  · have hb := hL.bits
    rw [hU.byte (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · have := hL.bits_w w hw; omega_arith
      · have := hI.bits w hw; omega_arith) (by omega_arith)]
    exact hF.bits t ht

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`, by the window method with
the table made affine, `inv` leaving `R.z^(p-2)` in `E.x`; only `invClob`,
`jwW` and what `inv` writes change. -/
theorem winJacA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr}
    (hI : InvSpecJ K C base size inv IW) {s₀ : State}
    (hs₀ : Scr s₀ base size) (hM₀ : ModOkW K.M size C.p s₀.mem base) (hF₀ : JacWinFixed K C base s₀ P k) :
    WP isa (K.windowA inv dbl).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (jwW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs₀.nowrap
  have hJ := hL.J
  obtain hP0 : P ≠ .infinity := by
    intro h
    have := hF₀.pt
    rw [h, hF₀.pz] at this
    exact hC.one_ne_zero this.2.2
  obtain pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [JacWinCfg.windowA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs₀ hM₀ hF₀.toJacWinPt) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (normA_ok hL hp hC hpn hone_lt hone hI F₁.scr F₁.mod T₁)
    fun s ⟨hs, Kn, Un, hM, T₂, O₂⟩ => ?_)
  obtain U₀ : Unch base (jwW K ++ IW) s₀.mem s.mem := (F₁.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  obtain hF : JacWinFixed K C base s P k := hF₀.unchA hL hI U₀ hn
  obtain K₀ : KeepRegs (invClob K.M.n) s₀ s := (F₁.keep.mono pc).trans Kn
  refine WP.seq (WP.mono (jfirst_ok hL hC hP hF hkJ (JFrame.refl hs hM) T₂) fun s₂ ⟨I₂, U₂⟩ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvA K C base size P s k 0 t)
    (Inv := fun j t => JInvA K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstepA_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hpn hone_lt hone hF h1 (by omega_arith) hi)
    (fun _ h => h) (by omega_arith) ⟨I₂, O₂.loopW hL U₂ hn⟩) fun s₃ ⟨I₃, _⟩ => ?_)
  obtain ⟨Q, -, hQe, R₃⟩ := I₃.st
  rw [Window5.winE_zero'] at hQe
  -- `Y = 1` where `Z = 0`.
  have hs₃ := R₃.fr.scr
  obtain hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [R₃.fr.ro hL (by jw_mem)]; exact hF.zero
  obtain ayz : K.R.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.R.y :=
    hL.ap (by jw_mem) (by jw_mem) (fun e => hL.ro K.zero (by jw_mem) (by rw [← e]; jw_mem))
  refine WP.seq (WP.mono (outFix_ok K.tc hs₃ hL.n0 (Nat.lt_trans hone_lt hpn)
    (show K.R.y + 8 * K.M.n ≤ size from hL.le (by jw_mem)) (show K.R.z + 8 * K.M.n ≤ size from hL.le (by jw_mem))
    (show K.zero + 8 * K.M.n ≤ size from hL.le (by jw_mem)) ayz hz₃) fun s₄ ⟨ey₄', k₄, O₄'⟩ => ?_)
  have ey₄ : wordsVal s₄.mem base K.R.y K.M.n = if wordsVal s₃.mem base K.R.z K.M.n = 0 then K.one
      else wordsVal s₃.mem base K.R.y K.M.n := ey₄'
  have O₄ : Outside base K.R.y (8 * K.M.n) s₃.mem s₄.mem := O₄'
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  obtain ex₄ : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₃.mem base K.R.x K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain ez₄ : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₃.mem base K.R.z K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 2) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain U₄ : Unch base (jwLoopW K) s₃.mem s₄.mem := O₄.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw]; exact other_loopW (by jw_mem)
  obtain F₄ := R₃.fr.next hL hs₄ (k₄.mono (sub_powClob (by decide))) U₄ (jwLoopW_sub K)
  obtain hlt₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₄]; exact R₃.lt _ (by simp)
    · rw [ey₄]; split
      · exact hone_lt
      · exact R₃.lt _ (by simp)
    · rw [ez₄]; exact R₃.lt _ (by simp)
  obtain hSlR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s₄) s₄ :=
    ⟨hs₄, F₄.mod, hSlR, hlt₄, fun _ _ => rfl⟩
  obtain hS : ∀ op ∈ K.tc.outOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain hR : readsOk K.tc.outOps [K.R.x, K.R.y, K.R.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out, JacWinCfg.tc]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ I₄ hS hR) fun s₅ ⟨P₅, I₅⟩ => ?_
  obtain hval : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      runOps K.tc.outOps (tmv C K.M.n base s₄) x ∧ wordsVal s₅.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ validAfter K.tc.outOps [K.R.x, K.R.y, K.R.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := P₅.loopW (by
    intro x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, FOp.out, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem))
  obtain F₅ := F₄.next hL (P₅.scr hs₄) P₅.regs U₅ (jwLoopW_sub K)
  refine ⟨K₀.trans (F₅.keep.mono pc), (U₀.trans F₅.unch).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
    F₅.mod, fun x hx => (hval x hx).2, fun hk => ?_⟩
  obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₅ x = runOps K.tc.outOps (tmv C K.M.n base s₄) x :=
    fun x hx => (hval x hx).1
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  obtain hxt : K.R.x ≠ K.S.t0 := hL.oth_ne (i := 0) (j := 7) (by decide) (by decide) (by decide)
  obtain hzt : K.R.z ≠ K.S.t0 := hL.oth_ne (i := 2) (j := 7) (by decide) (by decide) (by decide)
  obtain hxz : K.R.x ≠ K.R.z := hL.oth_ne (i := 0) (j := 2) (by decide) (by decide) (by decide)
  obtain hxy : K.R.x ≠ K.R.y := hL.oth_ne (i := 0) (j := 1) (by decide) (by decide) (by decide)
  obtain hyt : K.R.y ≠ K.S.t0 := hL.oth_ne (i := 1) (j := 7) (by decide) (by decide) (by decide)
  obtain hyz : K.R.y ≠ K.R.z := hL.oth_ne (i := 1) (j := 2) (by decide) (by decide) (by decide)
  simp only [TCombCfg.outOps, JacWinCfg.tc, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply, hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
  obtain hy : tmv C K.M.n base s₄ K.R.y = if tmv C K.M.n base s₃ K.R.z = 0 then 1
      else tmv C K.M.n base s₃ K.R.y := by
    show toM _ _ _ = _
    rw [ey₄]
    by_cases h : wordsVal s₃.mem base K.R.z K.M.n = 0
    · have h' : tmv C K.M.n base s₃ K.R.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
      simp only [h, h', ↓reduceIte]; exact hone
    · have h' : tmv C K.M.n base s₃ K.R.z ≠ 0 := fun h0 =>
        h ((toM_eq_zero_iff hp (R₃.lt _ (by simp))).mp h0)
      simp only [h, h', ↓reduceIte]
  obtain ex : tmv C K.M.n base s₄ K.R.x = tmv C K.M.n base s₃ K.R.x := by
    show toM _ _ _ = toM _ _ _; rw [ex₄]
  obtain ez : tmv C K.M.n base s₄ K.R.z = tmv C K.M.n base s₃ K.R.z := by
    show toM _ _ _ = toM _ _ _; rw [ez₄]
  rw [hy, ex, ez, ← hQe hk]
  exact InvJ.out hC R₃.rep

end VG.Proof.Weierstrass.X86_64
