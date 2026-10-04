import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps

/-!
# ECDSA on 32-bit ARM: where the ladder's and the powers' slots are

The slots of `c.ladderCfg`, `c.powP` and `c.powN` are numbered slots `c.sl i`
for distinct `i`, so they are apart as `ladder_ok` and `pow_ok` need
(`ladLay`, `powLayP`, `powLayN`): each fact is one about the numbers `i`,
which `decide` checks. The accumulator `c.wk` is above them all (`ladWk`,
`powWkP`, `powWkN`).
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} : c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) : (l.map c.sl).Nodup :=
  List.Pairwise.map c.sl (fun _ _ hab e => hab (sl_inj c hn e)) h

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : CfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n7 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

theorem ladSlots_eq (c : Cfg) : ladSlots c.ladderCfg = [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4,
    T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl

theorem ladLay (hc : CfgOk c) : LadLay c.ladderCfg size := by
  have hn := hc.n0
  have h7 := hc.n7
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, GX, GY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 16 by omega⟩,
    bitsAt_le c h7 (j := 0) (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, GX, GY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c (i := TMP) (by decide) 0 0)

theorem ladWk (hc : CfgOk c) : LadWk c.ladderCfg size c.wk where
  le := wk_le c hc.n7 rfl
  sl := by
    rw [ladSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ],
      i < 45 := by decide
    exact sl_below_wk c (this i hi)
  mo := sl_below_wk c (i := MP) (by decide)
  tmp := sl_below_wk c (i := TMP) (by decide)
  bits := bitsAt_below_wk c (j := 0) (by decide)

theorem powLay_of (hc : CfgOk c) {jm : Nat} (hjm : jm ∉ [ACC, PT, TMP])
    (minv : BitVec 64) {red : Red}
    {base one j : Nat} (hj : j < 3) (hb : base ∉ [ACC, PT, TMP]) (hb45 : base < 45) (ho : one ≠ ACC)
    (ho45 : one < 45) :
    PowLay ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one, bitsAt c.n j,
      64 * c.n⟩ size := by
  have hn := hc.n0
  have h7 := hc.n7
  have hw : ∀ i, i ∉ [ACC, PT, TMP] →
      ∀ w ∈ powW ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one,
        bitsAt c.n j, 64 * c.n⟩, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hi.1
    · exact sl_apart c hi.2.1
    · exact sl_apart c hi.2.2
  refine ⟨sl_le c h7 (by decide), sl_le c h7 (by decide), sl_le c h7 hb45, sl_le c h7 ho45,
    bitsAt_le c h7 hj, ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 16 by omega⟩,
    sl_apart c (by decide), sl_apart c (by decide), sl_apart c (Ne.symm ho), hw base hb, ?_,
    hw jm hjm⟩
  intro w hw'
  simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl <;> exact Or.inr (sl_below_bits c (by decide) j 0)

theorem powLayP (hc : CfgOk c) : PowLay c.powP size :=
  powLay_of hc (jm := MP) (by decide) _ (j := 1) (by decide) (base := RZ) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem powLayN (hc : CfgOk c) : PowLay c.powN size :=
  powLay_of hc (jm := MN) (by decide) _ (j := 2) (by decide) (base := KM) (by decide) (by decide)
    (one := ONEN) (by decide) (by decide)

theorem powWk_of (hc : CfgOk c) {jm : Nat} (hjm : jm < 45) (minv : BitVec 64) {red : Red}
    {base one j : Nat}
    (hj : j < 3) (hb45 : base < 45) :
    PowWk ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one, bitsAt c.n j,
      64 * c.n⟩ size c.wk :=
  ⟨wk_le c hc.n7 rfl, sl_below_wk c (by decide), sl_below_wk c (by decide), sl_below_wk c hb45,
    sl_below_wk c hjm, sl_below_wk c (by decide), bitsAt_below_wk c hj, sl_apart c (by decide)⟩

theorem powWkP (hc : CfgOk c) : PowWk c.powP size c.wk :=
  powWk_of hc (jm := MP) (by decide) _ (j := 1) (by decide) (base := RZ) (by decide)

theorem powWkN (hc : CfgOk c) : PowWk c.powN size c.wk :=
  powWk_of hc (jm := MN) (by decide) _ (j := 2) (by decide) (base := KM) (by decide)

end VG.Proof.Ecdsa.Arm
