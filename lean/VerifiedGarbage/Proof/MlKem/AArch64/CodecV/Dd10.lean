module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-!
# ML-KEM on AArch64: `dd10Half`

Two groups of 40 bits, in the doublewords of a register, split into their eight values of ten
bits, decompressed and stored (`dd10Half_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G)

theorem eval_trn1_s4 (x y : BitVec 128) :
    VPermOp.eval .trn1 .s4 x y = ofVWords (vword x 0) (vword y 0) (vword x 2) (vword y 2) := by
  have sw : ∀ w : BitVec 32, (w.setWidth 128).setWidth 32 = w := fun w => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceDiv]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.mul_zero, Nat.mul_one, sw]

theorem vword_trn1_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .trn1 .s4 x y) e = if e % 2 = 0 then vword x e else vword y (e - 1) := by
  rw [eval_trn1_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The value of ten bits `m` of two groups of 40 bits. -/
abbrev dig10 (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 4) / 2 ^ (10 * (m % 4)) % 2 ^ 10

/-- The words of `v` after TRN1 and the mask of 20 bits: the low and high 20 bits of each group. -/
abbrev V2 (Gv : Nat → Nat) (e : Nat) : Nat := if e % 2 = 0 then Gv (e / 2) % 2 ^ 32 else Gv (e / 2) / 2 ^ 20

/-- Value `m` of the two groups, as `dd10Half` computes it. -/
abbrev C10 (Gv : Nat → Nat) (m : Nat) : Nat :=
  if m < 4 then (if m % 2 = 0 then V2 Gv (m / 2) % 2 ^ 20 % 2 ^ 10 else V2 Gv (m / 2) % 2 ^ 20 / 2 ^ 10)
  else (if (m - 4) % 2 = 0 then V2 Gv (2 + (m - 4) / 2) % 2 ^ 20 % 2 ^ 10
    else V2 Gv (2 + (m - 4) / 2) % 2 ^ 20 / 2 ^ 10)

theorem split10 {Gv : Nat → Nat} (h0 : Gv 0 < 2 ^ 40) (h1 : Gv 1 < 2 ^ 40) {m : Nat} (hm : m < 8) :
    C10 Gv m = dig10 Gv m := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [C10, V2, dig10] <;> omega

theorem dd10Half_ok {s : State} {g : VReg} (hg : g = .v6 ∨ g = .v7) {o : Nat} (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16)
    (hc : DConsts 10 s) (h18 : Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 10 - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv) (hGv : ∀ l < 2, Gv l < 2 ^ 40)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 8 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 8, Gf (t + m) = BitVec.ofNat 32 (df 10 (dig10 Gv m)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ g → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd10Half g o ++ is)) s Q := by
  have g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  have g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  have g3 : g ≠ .v3 := by rcases hg with rfl | rfl <;> decide
  have g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  have g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  have g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  have g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  unfold dd10Half ddSplit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine wp_vop (eval_shift (by decide)) fun a1 h1 => wp_vop rfl fun a2 h2 => wp_vop rfl fun a3 h3' =>
    wp_vop (eval_shift (by decide)) fun a4 h4 => wp_vop rfl fun a5 h5 => wp_vop rfl fun a6 h6 =>
    wp_vop rfl fun a7 h7 => wp_nil ?_
  -- the low word and the high 20 bits of each group
  have A : ∀ l < 2, (vword (s.v g) (2 * l)).toNat = Gv l % 2 ^ 32 := fun l hl => by
    have w := vdword_words' (s.v g) l
    rw [hG l hl] at w
    have := (vword (s.v g) (2 * l + 1)).isLt
    omega
  have B : ∀ l < 2, (vword (a1.v .v1) (2 * l)).toNat = Gv l / 2 ^ 20 := fun l hl => by
    have dv : (vdword (a1.v .v1) l).toNat = Gv l / 2 ^ 20 := by
      rw [h1.v, StraightV.vdword_map2 _ _ _ hl]
      simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hG l hl]
    have w := vdword_words' (a1.v .v1) l
    rw [dv] at w
    have := hGv l hl
    have := (vword (a1.v .v1) (2 * l)).isLt
    have := (vword (a1.v .v1) (2 * l + 1)).isLt
    omega
  have L2 : Lanes (a2.v g) (V2 Gv) := fun e he => by
    rw [h2.v, vword_trn1_s4 _ _ he, h1.get g g1]
    simp only [V2]
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [ite_eq_left h, ite_eq_left h, show e = 2 * (e / 2) from by omega, A _ (by omega)]
      congr 2; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), show e - 1 = 2 * (e / 2) from by omega,
        B _ (by omega)]
  have L3 : Lanes (a3.v g) fun e => V2 Gv e % 2 ^ 20 := by
    rw [h3'.v]
    have l18 : Lanes (a2.v .v18) fun _ => 2 ^ 20 - 1 := by
      rw [h2.get .v18 g18.symm, h1.get .v18 (by decide)]; exact h18
    exact lanes_mask L2 l18
  have L4 : Lanes (a4.v .v1) fun e => V2 Gv e % 2 ^ 20 / 2 ^ 10 := by
    rw [h4.v]; exact lanes_ushr L3 10 _
  have L5 : Lanes (a5.v g) fun e => V2 Gv e % 2 ^ 20 % 2 ^ 10 := by
    have l3 : Lanes (a4.v g) fun e => V2 Gv e % 2 ^ 20 := by rw [h4.get g g1]; exact L3
    have l19 : Lanes (a4.v .v19) fun _ => 2 ^ 10 - 1 := by
      rw [h4.get .v19 (by decide), h3'.get .v19 g19.symm, h2.get .v19 g19.symm, h1.get .v19 (by decide)]
      exact h19
    rw [h5.v]
    exact lanes_mask l3 l19
  have L6 : Lanes (a7.v .v2) fun e => C10 Gv e := fun e he => by
    rw [h7.get .v2 (by decide), h6.v, vword_zip1_s4' _ _ he, h5.get .v1 g1.symm]
    simp only [C10, show e < 4 from he, ite_true]
    split
    · exact L5 _ (by omega)
    · exact L4 _ (by omega)
  have L7 : Lanes (a7.v .v3) fun e => C10 Gv (4 + e) := fun e he => by
    rw [h7.v, vword_zip2_s4 _ _ he, h6.get g g2, h6.get .v1 (by decide), h5.get .v1 g1.symm]
    simp only [C10, show ¬ 4 + e < 4 by omega, ite_false, show 4 + e - 4 = e by omega]
    split
    · exact L5 _ (by omega)
    · exact L4 _ (by omega)
  have cs7 : DConsts 10 a7 := hc.chg (((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans
    h5.chg).trans (h6.chg.trans h7.chg)) (by simp [g16.symm]) (by simp [g17.symm])
  have C10_lt : ∀ m < 8, C10 Gv m < 2 ^ 10 := fun m hm => by
    rw [split10 (hGv 0 (by decide)) (hGv 1 (by decide)) hm]; exact Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) cs7.q cs7.h (by decide) L6
    fun e he => C10_lt e (by omega)) fun b1 ⟨d1, r2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (cs7.chg d1).q (cs7.chg d1).h (by decide)
    (Lanes.chg d1 (by decide) L7) fun e he => C10_lt _ (by omega)) fun b2 ⟨d2, r3⟩ => ?_
  have c := ((((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans
    h7.chg).trans (d1.trans d2)
  simp only [List.cons_append, List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ho ht (by rw [c.mem]; exact hcu)
    (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg d2 (by decide) r2) fun e he => by
      rw [hval e (by omega), split10 (hGv 0 (by decide)) (hGv 1 (by decide)) (by omega)])
    (vword_G r3 fun e he => by
      rw [Nat.add_assoc, hval (4 + e) (by omega), split10 (hGv 0 (by decide)) (hGv 1 (by decide)) (by omega)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r a b d e => by rw [st.v, c.v r (by simp [a, b, d, e])]) o f

end VG.Proof.MlKem.AArch64.CodecV
