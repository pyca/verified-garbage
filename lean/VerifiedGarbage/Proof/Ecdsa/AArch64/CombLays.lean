import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb

/-!
# ECDSA on AArch64: the fixed-base comb's slots and constants

The comb's slots are numbered slots, apart as `comb_ok` needs (`combLay`),
and its constants, the Montgomery forms of the curve's tables, are what
`comb_ok` needs (`combVals`) if the tables are right (`CombOk`, which a
curve's own facts prove).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combJ (hc : CfgOk c) : c.combCfg.J = 16 * c.n := by
  show (c.tbl.map _).length = _; rw [List.length_map, hc.tbl_len]

theorem combW_eq (c : Cfg) : combW c.combCfg = slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
    T4, T5, DX, DY, DZ, TMP] := rfl

theorem combLay (hc : CfgOk c) : CombLay c.combCfg size := by
  have hn := hc.n0
  have h7 := hc.n7
  have hJ := combJ hc
  have hb := bitsAt_le c h7 (j := 0) (by decide)
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, BM, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, BM, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show bitsAt c.n 0 + 4 * (16 * c.n) ≤ 8192; omega
  · show bitsAt c.n 0 + 3 < 4096; omega
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    exact Or.inr (sl_below_bits c (hl i hi) 0 0)

theorem combA (c : Cfg) : CombA c.combCfg where
  sl := by
    have e : combSlots c.combCfg = [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ].map c.sl := rfl
    rw [e]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i
  mod := MP'_A c

theorem mont_zero (c : Cfg) : c.mont 0 = 0 := by simp [Cfg.mont]

theorem mont_lt (hc : CfgOk c) (x : Nat) : c.mont x < c.C.p :=
  Nat.mod_lt _ (by have := hc.p_ge; omega)

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (n : Nat) {d : α} {e : β} (he : f d = e) :
    (l.map f).getD n e = f (l.getD n d) := by
  subst he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[n]? <;> rfl

/-- The Montgomery forms of the tables' entries. -/
theorem combAt_mont (c : Cfg) (j m : Nat) :
    combAt c.combCfg.tbl j m = (c.mont (combAt c.tbl j m).1, c.mont (combAt c.tbl j m).2) := by
  show ((c.tbl.map fun t => t.map fun q => (c.mont q.1, c.mont q.2)).getD j []).getD m (0, 0) = _
  rw [getD_map' _ _ _ (d := []) (e := []) rfl,
    getD_map' _ _ _ (d := (0, 0)) (e := (0, 0)) (by simp [mont_zero])]
  rfl

/-- The comb's constants, from its tables' facts. -/
theorem combVals (hc : CfgOk c) (hC : Law c.C) (hT : CombOk c.C (16 * c.n) c.tbl c.start) :
    CombVals c.combCfg c.C where
  tbl_lt j _ i := by
    rw [getD_map_fst, getD_map_snd]
    have h := combAt_mont c j i
    unfold combAt at h
    rw [h]
    exact ⟨mont_lt hc _, mont_lt hc _⟩
  one_lt := mont_lt hc 1
  one := by
    show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1
    rw [toM_cmont hc]; rfl
  entry j hj m hm := by
    show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) _) (toM c.C.p (2 ^ (64 * c.n)) _) 1 _
    rw [combAt_mont, toM_cmont hc, toM_cmont hc]
    have := hT.entry j (by rw [combJ hc] at hj; exact hj) m hm
    rw [combPt, this]
    exact rep_affine' hC _ _
  start_lt := ⟨mont_lt hc _, mont_lt hc _⟩
  start := by
    show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (c.mont c.start.1))
      (toM c.C.p (2 ^ (64 * c.n)) (c.mont c.start.2)) 1 _
    rw [toM_cmont hc, toM_cmont hc, combJ hc, hT.start]
    exact rep_affine' hC _ _

theorem combClob_regs : ∀ n < 7, Reg.x0 ∉ combClob n ∧ Reg.x20 ∉ combClob n := by
  unfold combClob maskRegs clob acc; decide

theorem x0_not_combClob {n : Nat} (hn : n < 7) : Reg.x0 ∉ combClob n := (combClob_regs n hn).1

theorem x20_not_combClob {n : Nat} (hn : n < 7) : Reg.x20 ∉ combClob n := (combClob_regs n hn).2

end VG.Proof.Ecdsa.AArch64
