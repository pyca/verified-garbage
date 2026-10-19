module
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes

/-!
# ML-KEM on AArch64: `dd4Math`

The 32 nibbles of 16 bytes, split, interleaved, widened to words and decompressed.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- `Decompress_d` of a digit, as the code computes it. -/
abbrev df (d y : Nat) : Nat := (3329 * y + 2 ^ (d - 1)) / 2 ^ d

/-- The constants of `decV`. -/
structure DConsts (d : Nat) (s : State) : Prop where
  q : Lanes (s.v .v16) fun _ => 3329
  h : Lanes (s.v .v17) fun _ => 2 ^ (d - 1)

theorem DConsts.chg {d : Nat} {s t : State} (h : DConsts d s) {rs : List VReg} (c : VChg rs s t)
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : DConsts d t :=
  ⟨Lanes.chg c h16 h.q, Lanes.chg c h17 h.h⟩

/-- Nibble `i` of the bytes `B`. -/
abbrev nib (B : Nat → Nat) (i : Nat) : Nat := B (i / 2) / 16 ^ (i % 2) % 16

theorem vbyte_and_const {x y : BitVec 128} {j : Nat} (hy : (vbyte y j).toNat = 15) :
    (vbyte (x &&& y) j).toNat = (vbyte x j).toNat % 16 := by
  rw [Rc4.AArch64.vbyte_and, BitVec.toNat_and, hy, show (15 : Nat) = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem dd4Math_ok {s : State} (hc : DConsts 4 s) (h18 : ∀ j < 16, (vbyte (s.v .v18) j).toNat = 15)
    (h19 : s.v .v19 = 0) {B : Nat → Nat} (hB : ∀ j < 16, (vbyte (s.v .v0) j).toNat = B j)
    (hB' : ∀ j < 16, B j < 256) :
    WP isa (.block dd4Math) s fun t =>
      VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v20, .v21] s t ∧
      Lanes (t.v .v0) (fun e => df 4 (nib B e)) ∧ Lanes (t.v .v1) (fun e => df 4 (nib B (4 + e))) ∧
      Lanes (t.v .v2) (fun e => df 4 (nib B (8 + e))) ∧ Lanes (t.v .v3) (fun e => df 4 (nib B (12 + e))) ∧
      Lanes (t.v .v6) (fun e => df 4 (nib B (16 + e))) ∧ Lanes (t.v .v7) (fun e => df 4 (nib B (20 + e))) ∧
      Lanes (t.v .v20) (fun e => df 4 (nib B (24 + e))) ∧ Lanes (t.v .v21) (fun e => df 4 (nib B (28 + e))) := by
  unfold dd4Math
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_vop rfl fun a1 h1 => wp_vop (eval_shift (by decide)) fun a2 h2 => wp_vop rfl fun a3 h3 =>
    wp_vop rfl fun a4 h4 => wp_vop rfl fun a5 h5 => wp_vop rfl fun a6 h6 => wp_vop rfl fun a7 h7 =>
    wp_vop rfl fun a8 h8 => wp_vop rfl fun a9 h9 => wp_vop rfl fun a10 h10 => wp_vop rfl fun a11 h11 =>
    wp_vop rfl fun a12 h12 => wp_vop rfl fun a13 h13 => wp_vop rfl fun a14 h14 => wp_vop rfl fun a15 h15 =>
    wp_vop rfl fun a16 h16 => ?_
  -- the nibbles, as bytes
  have f1 : ∀ j < 16, (vbyte (a1.v .v1) j).toNat = B j % 16 := fun j hj => by
    rw [h1.v, vbyte_and_const (h18 j hj), hB j hj]
  have f2 : ∀ j < 16, (vbyte (a2.v .v2) j).toNat = B j / 16 := fun j hj => by
    rw [h2.v, Rc4.AArch64.vbyte_map2 _ _ _ hj, h1.get .v0 (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hB j hj]
  have n : ∀ i < 32, (if i % 2 = 0 then B (i / 2) % 16 else B (i / 2) / 16) = nib B i := fun i hi => by
    have := hB' (i / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [nib, h] <;> omega
  have f3 : ∀ i < 16, (vbyte (a3.v .v0) i).toNat = nib B i := fun i hi => by
    rw [h3.v, Blowfish.AArch64.vbyte_zip1 _ _ hi, h2.get .v1 (by decide), ← n i (by omega)]
    split <;> [exact f1 _ (by omega); exact f2 _ (by omega)]
  have f4 : ∀ i < 16, (vbyte (a4.v .v1) i).toNat = nib B (16 + i) := fun i hi => by
    rw [h4.v, Blowfish.AArch64.vbyte_zip2 _ _ hi, h3.get .v1 (by decide), h3.get .v2 (by decide),
      h2.get .v1 (by decide),
      ← n (16 + i) (by omega), show (16 + i) % 2 = i % 2 by omega, show (16 + i) / 2 = 8 + i / 2 by omega]
    split <;> [exact f1 _ (by omega); exact f2 _ (by omega)]
  -- the nibbles, as halfwords
  have z : ∀ (t : State), t.v .v19 = 0 → ∀ x, VPermOp.eval .zip1 .b16 x (t.v .v19) = VPermOp.eval .zip1 .b16 x 0 ∧
      VPermOp.eval .zip2 .b16 x (t.v .v19) = VPermOp.eval .zip2 .b16 x 0 := fun t ht x => by rw [ht]; simp
  have k19 : ∀ (t : State) (rs : List VReg), VChg rs s t → VReg.v19 ∉ rs → t.v .v19 = 0 := fun t rs c h => by
    rw [c.get .v19 h, h19]
  have c4 : VChg [.v1, .v2, .v0, .v1] s a4 := ((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg
  have g5 : ∀ k < 8, (vhalf (a5.v .v2) k).toNat = nib B k := fun k hk => by
    rw [h5.v, h4.get .v0 (by decide), (z a4 (k19 _ _ c4 (by decide)) _).1, (Cbd16.half_zip_zero _ hk).1,
      f3 k (by omega)]
  have g6 : ∀ k < 8, (vhalf (a6.v .v3) k).toNat = nib B (8 + k) := fun k hk => by
    rw [h6.v, h5.get .v0 (by decide), h4.get .v0 (by decide),
      (z a5 (k19 _ _ (c4.trans h5.chg) (by decide)) _).2, (Cbd16.half_zip_zero _ hk).2, f3 _ (by omega)]
  have g7 : ∀ k < 8, (vhalf (a7.v .v4) k).toNat = nib B (16 + k) := fun k hk => by
    rw [h7.v, h6.get .v1 (by decide), h5.get .v1 (by decide),
      (z a6 (k19 _ _ ((c4.trans h5.chg).trans h6.chg) (by decide)) _).1, (Cbd16.half_zip_zero _ hk).1,
      f4 _ (by omega)]
  have g8 : ∀ k < 8, (vhalf (a8.v .v5) k).toNat = nib B (24 + k) := fun k hk => by
    rw [h8.v, h7.get .v1 (by decide), h6.get .v1 (by decide), h5.get .v1 (by decide),
      (z a7 (k19 _ _ (((c4.trans h5.chg).trans h6.chg).trans h7.chg) (by decide)) _).2,
      (Cbd16.half_zip_zero _ hk).2, f4 _ (by omega), show 16 + (8 + k) = 24 + k by omega]
  -- the nibbles, as words
  have c8 : VChg ([.v1, .v2, .v0, .v1] ++ [.v2] ++ [.v3] ++ [.v4] ++ [.v5]) s a8 :=
    (((c4.trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg
  have hz : ∀ (t : State) (rs : List VReg), VChg rs s t → VReg.v19 ∉ rs → ∀ e < 8, vhalf (t.v .v19) e = 0 :=
    fun t rs c h e _ => by rw [k19 t rs c h]; simp [vhalf]
  have w9 : Lanes (a9.v .v0) fun k => nib B k := fun k hk => by
    rw [h9.v, (Ntt16.vword_zip_zero (hz _ _ c8 (by decide)) hk).1, h8.get .v2 (by decide),
      h7.get .v2 (by decide), h6.get .v2 (by decide), g5 k (by omega)]
  have c9 := c8.trans h9.chg
  have w10 : Lanes (a10.v .v1) fun k => nib B (4 + k) := fun k hk => by
    rw [h10.v, (Ntt16.vword_zip_zero (hz _ _ c9 (by decide)) hk).2, h9.get .v2 (by decide),
      h8.get .v2 (by decide), h7.get .v2 (by decide), h6.get .v2 (by decide), g5 _ (by omega)]
  have c10 := c9.trans h10.chg
  have w11 : Lanes (a11.v .v2) fun k => nib B (8 + k) := fun k hk => by
    rw [h11.v, (Ntt16.vword_zip_zero (hz _ _ c10 (by decide)) hk).1, h10.get .v3 (by decide),
      h9.get .v3 (by decide), h8.get .v3 (by decide), h7.get .v3 (by decide), g6 k (by omega)]
  have c11 := c10.trans h11.chg
  have w12 : Lanes (a12.v .v3) fun k => nib B (12 + k) := fun k hk => by
    rw [h12.v, (Ntt16.vword_zip_zero (hz _ _ c11 (by decide)) hk).2, h11.get .v3 (by decide),
      h10.get .v3 (by decide), h9.get .v3 (by decide), h8.get .v3 (by decide), h7.get .v3 (by decide),
      g6 _ (by omega), show 8 + (4 + k) = 12 + k by omega]
  have c12 := c11.trans h12.chg
  have w13 : Lanes (a13.v .v6) fun k => nib B (16 + k) := fun k hk => by
    rw [h13.v, (Ntt16.vword_zip_zero (hz _ _ c12 (by decide)) hk).1, h12.get .v4 (by decide),
      h11.get .v4 (by decide), h10.get .v4 (by decide), h9.get .v4 (by decide), h8.get .v4 (by decide),
      g7 k (by omega)]
  have c13 := c12.trans h13.chg
  have w14 : Lanes (a14.v .v7) fun k => nib B (20 + k) := fun k hk => by
    rw [h14.v, (Ntt16.vword_zip_zero (hz _ _ c13 (by decide)) hk).2, h13.get .v4 (by decide),
      h12.get .v4 (by decide), h11.get .v4 (by decide), h10.get .v4 (by decide), h9.get .v4 (by decide),
      h8.get .v4 (by decide), g7 _ (by omega), show 16 + (4 + k) = 20 + k by omega]
  have c14 := c13.trans h14.chg
  have w15 : Lanes (a15.v .v20) fun k => nib B (24 + k) := fun k hk => by
    rw [h15.v, (Ntt16.vword_zip_zero (hz _ _ c14 (by decide)) hk).1, h14.get .v5 (by decide),
      h13.get .v5 (by decide), h12.get .v5 (by decide), h11.get .v5 (by decide), h10.get .v5 (by decide),
      h9.get .v5 (by decide), g8 k (by omega)]
  have c15 := c14.trans h15.chg
  have w16 : Lanes (a16.v .v21) fun k => nib B (28 + k) := fun k hk => by
    rw [h16.v, (Ntt16.vword_zip_zero (hz _ _ c15 (by decide)) hk).2, h15.get .v5 (by decide),
      h14.get .v5 (by decide), h13.get .v5 (by decide), h12.get .v5 (by decide), h11.get .v5 (by decide),
      h10.get .v5 (by decide), h9.get .v5 (by decide), g8 _ (by omega), show 24 + (4 + k) = 28 + k by omega]
  have c16 := c15.trans h16.chg
  -- the words at the end of the permutations
  have u0 : Lanes (a16.v .v0) fun k => nib B k := Lanes.chg (h10.chg.trans (h11.chg.trans (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg)))))) (by decide) w9
  have u1 : Lanes (a16.v .v1) fun k => nib B (4 + k) := Lanes.chg (h11.chg.trans (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg))))) (by decide) w10
  have u2 : Lanes (a16.v .v2) fun k => nib B (8 + k) := Lanes.chg (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg)))) (by decide) w11
  have u3 : Lanes (a16.v .v3) fun k => nib B (12 + k) := Lanes.chg
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg))) (by decide) w12
  have u6 : Lanes (a16.v .v6) fun k => nib B (16 + k) := Lanes.chg
    (h14.chg.trans (h15.chg.trans h16.chg)) (by decide) w13
  have u7 : Lanes (a16.v .v7) fun k => nib B (20 + k) := Lanes.chg (h15.chg.trans h16.chg) (by decide) w14
  have u20 : Lanes (a16.v .v20) fun k => nib B (24 + k) := Lanes.chg h16.chg (by decide) w15
  have hc16 : DConsts 4 a16 := hc.chg c16
  have nb : ∀ i, nib B i < 2 ^ 4 := fun i => Nat.mod_lt _ (by decide)
  -- the decompressions
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v0) (by decide) (by decide) hc16.q hc16.h (by decide) u0 fun _ _ => nb _)
    fun b1 ⟨d1, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v1) (by decide) (by decide) (hc16.chg d1).q (hc16.chg d1).h (by decide)
    (Lanes.chg d1 (by decide) u1) fun _ _ => nb _) fun b2 ⟨d2, r1⟩ => ?_
  have e2 := d1.trans d2
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) (hc16.chg e2).q (hc16.chg e2).h (by decide)
    (Lanes.chg e2 (by decide) u2) fun _ _ => nb _) fun b3 ⟨d3, r2⟩ => ?_
  have e3 := e2.trans d3
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (hc16.chg e3).q (hc16.chg e3).h (by decide)
    (Lanes.chg e3 (by decide) u3) fun _ _ => nb _) fun b4 ⟨d4, r3⟩ => ?_
  have e4 := e3.trans d4
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v6) (by decide) (by decide) (hc16.chg e4).q (hc16.chg e4).h (by decide)
    (Lanes.chg e4 (by decide) u6) fun _ _ => nb _) fun b5 ⟨d5, r6⟩ => ?_
  have e5 := e4.trans d5
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v7) (by decide) (by decide) (hc16.chg e5).q (hc16.chg e5).h (by decide)
    (Lanes.chg e5 (by decide) u7) fun _ _ => nb _) fun b6 ⟨d6, r7⟩ => ?_
  have e6 := e5.trans d6
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v20) (by decide) (by decide) (hc16.chg e6).q (hc16.chg e6).h (by decide)
    (Lanes.chg e6 (by decide) u20) fun _ _ => nb _) fun b7 ⟨d7, r20⟩ => ?_
  have e7 := e6.trans d7
  refine WP.mono (decV_ok (v := .v21) (by decide) (by decide) (hc16.chg e7).q (hc16.chg e7).h (by decide)
    (Lanes.chg e7 (by decide) w16) fun _ _ => nb _) fun t ⟨d8, r21⟩ => ⟨(c16.trans (e7.trans d8)).mono,
      Lanes.chg (d2.trans (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans d8)))))) (by decide) r0,
      Lanes.chg (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans d8))))) (by decide) r1,
      Lanes.chg (d4.trans (d5.trans (d6.trans (d7.trans d8)))) (by decide) r2,
      Lanes.chg (d5.trans (d6.trans (d7.trans d8))) (by decide) r3,
      Lanes.chg (d6.trans (d7.trans d8)) (by decide) r6, Lanes.chg (d7.trans d8) (by decide) r7,
      Lanes.chg d8 (by decide) r20, r21⟩

end VG.Proof.MlKem.AArch64.CodecV
