module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-!
# ML-KEM on AArch64: `ddSplit`

Two groups of `4 b` bits, in the doublewords of a register, split into their eight values of `b`
bits (`ddSplit_ok`): USHR by `2 b` and TRN1 put the low and high halves of each group in words,
which AND masks to `2 b` bits and USHR and AND split into values of `b` bits, which ZIP1 and ZIP2
put in order.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

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

/-- The value of `b` bits `m` of two groups of `4 b` bits. -/
abbrev dig (b : Nat) (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 4) / 2 ^ (b * (m % 4)) % 2 ^ b

/-- The words of `v` after TRN1: the low word and the high `2 b` bits of each group. -/
abbrev V2 (b : Nat) (Gv : Nat → Nat) (e : Nat) : Nat :=
  if e % 2 = 0 then Gv (e / 2) % 2 ^ 32 else Gv (e / 2) / 2 ^ (2 * b)

/-- Value `m` of the two groups, as `ddSplit` computes it. -/
abbrev CS (b : Nat) (Gv : Nat → Nat) (m : Nat) : Nat :=
  if m < 4 then (if m % 2 = 0 then V2 b Gv (m / 2) % 2 ^ (2 * b) % 2 ^ b else V2 b Gv (m / 2) % 2 ^ (2 * b) / 2 ^ b)
  else (if (m - 4) % 2 = 0 then V2 b Gv (2 + (m - 4) / 2) % 2 ^ (2 * b) % 2 ^ b
    else V2 b Gv (2 + (m - 4) / 2) % 2 ^ (2 * b) / 2 ^ b)

theorem splitCS {b : Nat} (hb : b = 10 ∨ b = 11) {Gv : Nat → Nat} (h0 : Gv 0 < 2 ^ (4 * b))
    (h1 : Gv 1 < 2 ^ (4 * b)) {m : Nat} (hm : m < 8) : CS b Gv m = dig b Gv m := by
  rcases hb with rfl | rfl <;>
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [CS, V2, dig] at h0 h1 ⊢ <;> omega

theorem ddSplit_ok {s : State} {b : Nat} (hb : b = 10 ∨ b = 11) {g : VReg}
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ (2 * b) - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ b - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv) (hGv : ∀ l < 2, Gv l < 2 ^ (4 * b))
    {is : List Instr} {Q : State → Prop}
    (g1 : g ≠ .v1 := by decide) (g2 : g ≠ .v2 := by decide)
    (g18 : g ≠ .v18 := by decide) (g19 : g ≠ .v19 := by decide)
    (k : ∀ s', VChg [g, .v1, .v2, .v3] s s' → Lanes (s'.v .v2) (fun e => dig b Gv e) →
      Lanes (s'.v .v3) (fun e => dig b Gv (4 + e)) → WP isa (.block is) s' Q) :
    WP isa (.block (ddSplit b g ++ is)) s Q := by
  have hb22 : 2 * b < 32 := by omega
  have hsh1 : VShiftOp.ok .ushr VArr.d2.esize (2 * b) = true := by
    rcases hb with rfl | rfl <;> decide
  have hsh2 : VShiftOp.ok .ushr VArr.s4.esize b = true := by
    rcases hb with rfl | rfl <;> decide
  unfold ddSplit
  simp only [List.cons_append, List.nil_append]
  refine wp_vop (eval_shift hsh1) fun a1 h1 => wp_vop rfl fun a2 h2 => wp_vop rfl fun a3 h3' =>
    wp_vop (eval_shift hsh2) fun a4 h4 => wp_vop rfl fun a5 h5 => wp_vop rfl fun a6 h6 =>
    wp_vop rfl fun a7 h7 => ?_
  have pw : 2 ^ (2 * b) ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) (by omega)
  have pw4 : 2 ^ (4 * b) = 2 ^ (2 * b) * 2 ^ (2 * b) := by rw [← Nat.pow_add]; congr 1; omega
  -- the low word and the high `2 b` bits of each group
  have A : ∀ l < 2, (vword (s.v g) (2 * l)).toNat = Gv l % 2 ^ 32 := fun l hl => by
    have w := vdword_words' (s.v g) l
    rw [hG l hl] at w
    have := (vword (s.v g) (2 * l + 1)).isLt
    omega
  have B : ∀ l < 2, (vword (a1.v .v1) (2 * l)).toNat = Gv l / 2 ^ (2 * b) := fun l hl => by
    have dv : (vdword (a1.v .v1) l).toNat = Gv l / 2 ^ (2 * b) := by
      rw [h1.v, StraightV.vdword_map2 _ _ _ hl]
      simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hG l hl]
    have w := vdword_words' (a1.v .v1) l
    rw [dv] at w
    have lt : Gv l / 2 ^ (2 * b) < 2 ^ 22 := by
      have := hGv l hl
      rw [pw4] at this
      exact Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr this) pw
    have := (vword (a1.v .v1) (2 * l)).isLt
    have := (vword (a1.v .v1) (2 * l + 1)).isLt
    omega
  have L2 : Lanes (a2.v g) (V2 b Gv) := fun e he => by
    rw [h2.v, vword_trn1_s4 _ _ he, h1.get g g1]
    simp only [V2]
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [ite_eq_left h, ite_eq_left h, show e = 2 * (e / 2) from by omega, A _ (by omega)]
      congr 2; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), show e - 1 = 2 * (e / 2) from by omega,
        B _ (by omega)]
  have L3 : Lanes (a3.v g) fun e => V2 b Gv e % 2 ^ (2 * b) := by
    rw [h3'.v]
    have l18 : Lanes (a2.v .v18) fun _ => 2 ^ (2 * b) - 1 := by
      rw [h2.get .v18 g18.symm, h1.get .v18 (by decide)]; exact h18
    exact lanes_mask L2 l18
  have L4 : Lanes (a4.v .v1) fun e => V2 b Gv e % 2 ^ (2 * b) / 2 ^ b := by
    rw [h4.v]; exact lanes_ushr L3 b _
  have L5 : Lanes (a5.v g) fun e => V2 b Gv e % 2 ^ (2 * b) % 2 ^ b := by
    have l3 : Lanes (a4.v g) fun e => V2 b Gv e % 2 ^ (2 * b) := by rw [h4.get g g1]; exact L3
    have l19 : Lanes (a4.v .v19) fun _ => 2 ^ b - 1 := by
      rw [h4.get .v19 (by decide), h3'.get .v19 g19.symm, h2.get .v19 g19.symm, h1.get .v19 (by decide)]
      exact h19
    rw [h5.v]
    exact lanes_mask l3 l19
  have L6 : Lanes (a7.v .v2) fun e => CS b Gv e := fun e he => by
    rw [h7.get .v2 (by decide), h6.v, vword_zip1_s4' _ _ he, h5.get .v1 g1.symm]
    simp only [CS, show e < 4 from he, ite_true]
    split
    · exact L5 _ (by omega)
    · exact L4 _ (by omega)
  have L7 : Lanes (a7.v .v3) fun e => CS b Gv (4 + e) := fun e he => by
    rw [h7.v, vword_zip2_s4 _ _ he, h6.get g g2, h6.get .v1 (by decide), h5.get .v1 g1.symm]
    simp only [CS, show ¬ 4 + e < 4 by omega, ite_false, show 4 + e - 4 = e by omega]
    split
    · exact L5 _ (by omega)
    · exact L4 _ (by omega)
  refine k a7 ((((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans h5.chg).trans
    (h6.chg.trans h7.chg)).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hr ⊢
      rcases hr with h | h | h | h | h | h | h <;> simp [h]))
    (L6.congr fun e he => splitCS hb (hGv 0 (by decide)) (hGv 1 (by decide)) (by omega))
    (L7.congr fun e he => splitCS hb (hGv 0 (by decide)) (hGv 1 (by decide)) (by omega))

end VG.Proof.MlKem.AArch64.CodecV
