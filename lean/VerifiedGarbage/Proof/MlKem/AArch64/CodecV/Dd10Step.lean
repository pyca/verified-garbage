module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.TCB.AArch64.Simd
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Width
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlKem.AArch64.CodecV.DdStore`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.CodecV.DdSpec`, which this module and modules that import it used -/

section

/-!
# ML-KEM on AArch64: what `vg_mlkem_decode_decompress` reads and writes

Group `g` of the input is the number whose bytes are its bytes (`num g nb`), and coefficient `e`
of the group is its base-`2ᵈ` digit `e` (`byteDecode_group`), decompressed (`G_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (w : Width) (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x3
abbrev bR : Region := ⟨bP s₀, 32 * w.d⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (32 * w.d)
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B w s₀).getD j 0).toNat
/-- The first `j` bytes of group `g`, as a little-endian number. -/
def num (g j : Nat) : Nat := digits 8 ((List.range j).map fun j' => byte w s₀ (w.nb * g + j'))
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress w.d (B w s₀))[i]!).val
/-- The output's coefficients before. -/
def old (i : Nat) : BitVec 32 := coeffAt s₀.mem (fP s₀) i

end

structure Pre (w : Width) (s₀ : State) : Prop where
  rd : s₀.rd = [bR w s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR w s₀).Disjoint (polyRegion (fP s₀))

theorem num_succ (w : Width) (s₀ : State) (g j : Nat) :
    num w s₀ g (j + 1) = num w s₀ g j + 2 ^ (8 * j) * byte w s₀ (w.nb * g + j) :=
  digits_range_succ _ _ _

theorem cg_lt {w : Width} (hw : WOk w) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    w.c * g + e < 256 := by
  have := hw.cG
  have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega_arith

theorem nbg_le {w : Width} (hw : WOk w) {g : Nat} (hg : g < 256 / w.c) :
    w.nb * g + w.nb ≤ 32 * w.d := by
  have := hw.bytes
  have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega_arith

/-- Coefficient `e` of group `g` of the output. -/
theorem G_eq {w : Width} (hw : WOk w) (s₀ : State) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    G w s₀ (w.c * g + e) =
      BitVec.ofNat 32 ((q * (num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d) + 2 ^ (w.d - 1)) / 2 ^ w.d) := by
  have hi := cg_lt hw hg he
  have hd12 : w.d < 12 := by have := hw.d_le; omega_using [this]
  rw [G, decodeDecompress_get _ _ (show _ < n from hi),
    byteDecode_group hw.dc _ he (show _ < n from hi), bytes_map_take_drop _ (by
      rw [bytesAt_length]; exact nbg_le hw hg), ite_eq_left hd12, Nat.mod_mod,
    (decompress_val_of_le hw.d_pos hw.d_le (Nat.mod_lt _ (Nat.two_pow_pos _))).1]
  rfl

theorem Pre.byte_eq {w : Width} {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {j : Nat} (hj : j < 32 * w.d) (hw : w.d ≤ 11) :
    (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte w s₀ j := by
  rw [byte_frame (len := 32 * w.d) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by omega_using [hw]) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) (32 * w.d)).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

end VG.Proof.MlKem.AArch64.DD

end

end

/-! ### `MlKem.AArch64.CodecV.DdLoop`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.CodecV.Dd4`, which this module and modules that import it used -/

section

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
  obtain f1 : ∀ j < 16, (vbyte (a1.v .v1) j).toNat = B j % 16 := fun j hj => by
    rw [h1.v, vbyte_and_const (h18 j hj), hB j hj]
  obtain f2 : ∀ j < 16, (vbyte (a2.v .v2) j).toNat = B j / 16 := fun j hj => by
    rw [h2.v, Rc4.AArch64.vbyte_map2 _ _ _ hj, h1.get .v0 (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hB j hj]
  obtain n : ∀ i < 32, (if i % 2 = 0 then B (i / 2) % 16 else B (i / 2) / 16) = nib B i := fun i hi => by
    have := hB' (i / 2) (by omega_arith)
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [nib, h] <;> omega_arith
  obtain f3 : ∀ i < 16, (vbyte (a3.v .v0) i).toNat = nib B i := fun i hi => by
    rw [h3.v, Blowfish.AArch64.vbyte_zip1 _ _ hi, h2.get .v1 (by decide), ← n i (by omega_arith)]
    split <;> [exact f1 _ (by omega_arith); exact f2 _ (by omega_arith)]
  obtain f4 : ∀ i < 16, (vbyte (a4.v .v1) i).toNat = nib B (16 + i) := fun i hi => by
    rw [h4.v, Blowfish.AArch64.vbyte_zip2 _ _ hi, h3.get .v1 (by decide), h3.get .v2 (by decide),
      h2.get .v1 (by decide),
      ← n (16 + i) (by omega_arith), show (16 + i) % 2 = i % 2 by omega_arith, show (16 + i) / 2 = 8 + i / 2 by omega_arith]
    split <;> [exact f1 _ (by omega_arith); exact f2 _ (by omega_arith)]
  -- the nibbles, as halfwords
  obtain z : ∀ (t : State), t.v .v19 = 0 → ∀ x, VPermOp.eval .zip1 .b16 x (t.v .v19) = VPermOp.eval .zip1 .b16 x 0 ∧
      VPermOp.eval .zip2 .b16 x (t.v .v19) = VPermOp.eval .zip2 .b16 x 0 := fun t ht x => by rw [ht]; simp
  obtain k19 : ∀ (t : State) (rs : List VReg), VChg rs s t → VReg.v19 ∉ rs → t.v .v19 = 0 := fun t rs c h => by
    rw [c.get .v19 h, h19]
  obtain c4 : VChg [.v1, .v2, .v0, .v1] s a4 := ((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg
  obtain g5 : ∀ k < 8, (vhalf (a5.v .v2) k).toNat = nib B k := fun k hk => by
    rw [h5.v, h4.get .v0 (by decide), (z a4 (k19 _ _ c4 (by decide)) _).1, (Cbd16.half_zip_zero _ hk).1,
      f3 k (by omega_arith)]
  obtain g6 : ∀ k < 8, (vhalf (a6.v .v3) k).toNat = nib B (8 + k) := fun k hk => by
    rw [h6.v, h5.get .v0 (by decide), h4.get .v0 (by decide),
      (z a5 (k19 _ _ (c4.trans h5.chg) (by decide)) _).2, (Cbd16.half_zip_zero _ hk).2, f3 _ (by omega_arith)]
  obtain g7 : ∀ k < 8, (vhalf (a7.v .v4) k).toNat = nib B (16 + k) := fun k hk => by
    rw [h7.v, h6.get .v1 (by decide), h5.get .v1 (by decide),
      (z a6 (k19 _ _ ((c4.trans h5.chg).trans h6.chg) (by decide)) _).1, (Cbd16.half_zip_zero _ hk).1,
      f4 _ (by omega_arith)]
  obtain g8 : ∀ k < 8, (vhalf (a8.v .v5) k).toNat = nib B (24 + k) := fun k hk => by
    rw [h8.v, h7.get .v1 (by decide), h6.get .v1 (by decide), h5.get .v1 (by decide),
      (z a7 (k19 _ _ (((c4.trans h5.chg).trans h6.chg).trans h7.chg) (by decide)) _).2,
      (Cbd16.half_zip_zero _ hk).2, f4 _ (by omega_arith), show 16 + (8 + k) = 24 + k by omega_arith]
  -- the nibbles, as words
  obtain c8 : VChg ([.v1, .v2, .v0, .v1] ++ [.v2] ++ [.v3] ++ [.v4] ++ [.v5]) s a8 :=
    (((c4.trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg
  obtain hz : ∀ (t : State) (rs : List VReg), VChg rs s t → VReg.v19 ∉ rs → ∀ e < 8, vhalf (t.v .v19) e = 0 :=
    fun t rs c h e _ => by rw [k19 t rs c h]; simp [vhalf]
  obtain w9 : Lanes (a9.v .v0) fun k => nib B k := fun k hk => by
    rw [h9.v, (Ntt16.vword_zip_zero (hz _ _ c8 (by decide)) hk).1, h8.get .v2 (by decide),
      h7.get .v2 (by decide), h6.get .v2 (by decide), g5 k (by omega_arith)]
  obtain c9 := c8.trans h9.chg
  obtain w10 : Lanes (a10.v .v1) fun k => nib B (4 + k) := fun k hk => by
    rw [h10.v, (Ntt16.vword_zip_zero (hz _ _ c9 (by decide)) hk).2, h9.get .v2 (by decide),
      h8.get .v2 (by decide), h7.get .v2 (by decide), h6.get .v2 (by decide), g5 _ (by omega_arith)]
  obtain c10 := c9.trans h10.chg
  obtain w11 : Lanes (a11.v .v2) fun k => nib B (8 + k) := fun k hk => by
    rw [h11.v, (Ntt16.vword_zip_zero (hz _ _ c10 (by decide)) hk).1, h10.get .v3 (by decide),
      h9.get .v3 (by decide), h8.get .v3 (by decide), h7.get .v3 (by decide), g6 k (by omega_arith)]
  obtain c11 := c10.trans h11.chg
  obtain w12 : Lanes (a12.v .v3) fun k => nib B (12 + k) := fun k hk => by
    rw [h12.v, (Ntt16.vword_zip_zero (hz _ _ c11 (by decide)) hk).2, h11.get .v3 (by decide),
      h10.get .v3 (by decide), h9.get .v3 (by decide), h8.get .v3 (by decide), h7.get .v3 (by decide),
      g6 _ (by omega_arith), show 8 + (4 + k) = 12 + k by omega_arith]
  obtain c12 := c11.trans h12.chg
  obtain w13 : Lanes (a13.v .v6) fun k => nib B (16 + k) := fun k hk => by
    rw [h13.v, (Ntt16.vword_zip_zero (hz _ _ c12 (by decide)) hk).1, h12.get .v4 (by decide),
      h11.get .v4 (by decide), h10.get .v4 (by decide), h9.get .v4 (by decide), h8.get .v4 (by decide),
      g7 k (by omega_arith)]
  obtain c13 := c12.trans h13.chg
  obtain w14 : Lanes (a14.v .v7) fun k => nib B (20 + k) := fun k hk => by
    rw [h14.v, (Ntt16.vword_zip_zero (hz _ _ c13 (by decide)) hk).2, h13.get .v4 (by decide),
      h12.get .v4 (by decide), h11.get .v4 (by decide), h10.get .v4 (by decide), h9.get .v4 (by decide),
      h8.get .v4 (by decide), g7 _ (by omega_arith), show 16 + (4 + k) = 20 + k by omega_arith]
  obtain c14 := c13.trans h14.chg
  obtain w15 : Lanes (a15.v .v20) fun k => nib B (24 + k) := fun k hk => by
    rw [h15.v, (Ntt16.vword_zip_zero (hz _ _ c14 (by decide)) hk).1, h14.get .v5 (by decide),
      h13.get .v5 (by decide), h12.get .v5 (by decide), h11.get .v5 (by decide), h10.get .v5 (by decide),
      h9.get .v5 (by decide), g8 k (by omega_arith)]
  obtain c15 := c14.trans h15.chg
  obtain w16 : Lanes (a16.v .v21) fun k => nib B (28 + k) := fun k hk => by
    rw [h16.v, (Ntt16.vword_zip_zero (hz _ _ c15 (by decide)) hk).2, h15.get .v5 (by decide),
      h14.get .v5 (by decide), h13.get .v5 (by decide), h12.get .v5 (by decide), h11.get .v5 (by decide),
      h10.get .v5 (by decide), h9.get .v5 (by decide), g8 _ (by omega_arith), show 24 + (4 + k) = 28 + k by omega_arith]
  obtain c16 := c15.trans h16.chg
  -- the words at the end of the permutations
  obtain u0 : Lanes (a16.v .v0) fun k => nib B k := Lanes.chg (h10.chg.trans (h11.chg.trans (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg)))))) (by decide) w9
  obtain u1 : Lanes (a16.v .v1) fun k => nib B (4 + k) := Lanes.chg (h11.chg.trans (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg))))) (by decide) w10
  obtain u2 : Lanes (a16.v .v2) fun k => nib B (8 + k) := Lanes.chg (h12.chg.trans
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg)))) (by decide) w11
  have u3 : Lanes (a16.v .v3) fun k => nib B (12 + k) := Lanes.chg
    (h13.chg.trans (h14.chg.trans (h15.chg.trans h16.chg))) (by decide) w12
  have u6 : Lanes (a16.v .v6) fun k => nib B (16 + k) := Lanes.chg
    (h14.chg.trans (h15.chg.trans h16.chg)) (by decide) w13
  obtain u7 : Lanes (a16.v .v7) fun k => nib B (20 + k) := Lanes.chg (h15.chg.trans h16.chg) (by decide) w14
  obtain u20 : Lanes (a16.v .v20) fun k => nib B (24 + k) := Lanes.chg h16.chg (by decide) w15
  obtain hc16 : DConsts 4 a16 := hc.chg c16
  obtain nb : ∀ i, nib B i < 2 ^ 4 := fun i => Nat.mod_lt _ (by decide)
  -- the decompressions
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v0) (by decide) (by decide) hc16.q hc16.h (by decide) u0 fun _ _ => nb _)
    fun b1 ⟨d1, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v1) (by decide) (by decide) (hc16.chg d1).q (hc16.chg d1).h (by decide)
    (Lanes.chg d1 (by decide) u1) fun _ _ => nb _) fun b2 ⟨d2, r1⟩ => ?_
  obtain e2 := d1.trans d2
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) (hc16.chg e2).q (hc16.chg e2).h (by decide)
    (Lanes.chg e2 (by decide) u2) fun _ _ => nb _) fun b3 ⟨d3, r2⟩ => ?_
  obtain e3 := e2.trans d3
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (hc16.chg e3).q (hc16.chg e3).h (by decide)
    (Lanes.chg e3 (by decide) u3) fun _ _ => nb _) fun b4 ⟨d4, r3⟩ => ?_
  obtain e4 := e3.trans d4
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v6) (by decide) (by decide) (hc16.chg e4).q (hc16.chg e4).h (by decide)
    (Lanes.chg e4 (by decide) u6) fun _ _ => nb _) fun b5 ⟨d5, r6⟩ => ?_
  obtain e5 := e4.trans d5
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v7) (by decide) (by decide) (hc16.chg e5).q (hc16.chg e5).h (by decide)
    (Lanes.chg e5 (by decide) u7) fun _ _ => nb _) fun b6 ⟨d6, r7⟩ => ?_
  obtain e6 := e5.trans d6
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v20) (by decide) (by decide) (hc16.chg e6).q (hc16.chg e6).h (by decide)
    (Lanes.chg e6 (by decide) u20) fun _ _ => nb _) fun b7 ⟨d7, r20⟩ => ?_
  obtain e7 := e6.trans d7
  refine WP.mono (decV_ok (v := .v21) (by decide) (by decide) (hc16.chg e7).q (hc16.chg e7).h (by decide)
    (Lanes.chg e7 (by decide) w16) fun _ _ => nb _) fun t ⟨d8, r21⟩ => ⟨(c16.trans (e7.trans d8)).mono,
      Lanes.chg (d2.trans (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans d8)))))) (by decide) r0,
      Lanes.chg (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans d8))))) (by decide) r1,
      Lanes.chg (d4.trans (d5.trans (d6.trans (d7.trans d8)))) (by decide) r2,
      Lanes.chg (d5.trans (d6.trans (d7.trans d8))) (by decide) r3,
      Lanes.chg (d6.trans (d7.trans d8)) (by decide) r6, Lanes.chg (d7.trans d8) (by decide) r7,
      Lanes.chg d8 (by decide) r20, r21⟩

end VG.Proof.MlKem.AArch64.CodecV

end

end

/-!
# ML-KEM on AArch64: the loop of the vector decompression

After `k` iterations of a body that decompresses `G` groups of a width `w` (`DInv`): the
output's first `w.c · G · k` coefficients are written. The input's bytes in a vector
(`DInv.vbyte`), the end of a body (`dtail_ok`), and the loop (`dloop_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_movImm9 movImm_noV)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- After `k` iterations of `G` groups each, with constants `K` besides those of `decV`. -/
structure DInv (w : Width) (Ng : Nat) (K : State → Prop) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * k)
  x3 : s.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * k)
  x11 : (s.gpr .x11).toNat = 256 / (w.c * Ng) - k
  cs : DConsts w.d s
  K : K s
  out : CoeffsUpTo s.mem (fP s₀) (w.c * Ng * k) (DD.G w s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

/-- The 16 bytes of the input at byte `o`, loaded. -/
theorem vbyte_input {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {o : Nat} (ho : o + 16 ≤ 32 * w.d) {j : Nat} (hj : j < 16) :
    (vbyte (m.read (bP s₀ + BitVec.ofNat 64 o) 16) j).toNat = byte w s₀ (o + j) := by
  change ((m.read _ 16).extractLsb' (8 * j) 8).toNat = _
  rw [Mem.extractLsb'_read m _ hj, ptr_add, hp.byte_eq hf (by omega_using [ho, hj]) hw.d_le]

theorem DInv.in16 {w : Width} (hw : WOk w) {Ng : Nat} {K : State → Prop} {s₀ : State} (hp : Pre w s₀) {k : Nat}
    {s : State} (h : DInv w Ng K s₀ k s) {o : Nat} (ho : o + 16 ≤ 32 * w.d) :
    InRegions (s.rd ++ s.wr) (bP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  have := hw.d_le
  exact in_rd (in_regions (List.mem_singleton_self _) (contains_off ho (by omega_using [this])))

theorem DInv.out16 {w : Width} {Ng : Nat} {K : State → Prop} {s₀ : State} (hp : Pre w s₀) {k : Nat}
    {s : State} (h : DInv w Ng K s₀ k s) {i : Nat} (hi : i + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (fP s₀) i) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hi]) (by decide))

/-- A vector of four output coefficients, from their values. -/
theorem vword_G {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) {g : Nat → BitVec 32}
    (hg : ∀ e < 4, g e = BitVec.ofNat 32 (f e)) : ∀ e < 4, vword x e = g e := fun e he => by
  rw [hg e he]; apply BitVec.eq_of_toNat_eq; rw [hx e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt he)]

/-- The pointer and count updates at the end of a body. -/
theorem dtail_ok {w : Width} {Ng : Nat} {s₀ : State} {k : Nat} (hk : k < 256 / (w.c * Ng)) {s : State}
    (h0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * k)) (h3 : s.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * k))
    (h11 : (s.gpr .x11).toNat = 256 / (w.c * Ng) - k) (hi : 4 * (w.c * Ng) < 4096) (hb : w.nb * Ng < 4096) :
    WP isa (.block [.addImm .x .x0 .x0 (w.nb * Ng), .addImm .x .x3 .x3 (4 * (w.c * Ng)),
      .subImm .x .x11 .x11 1]) s fun t => Only [.x0, .x3, .x11] s t ∧ t.v = s.v ∧
      t.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * (k + 1)) ∧
      t.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * Ng) - (k + 1) ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 256 / (w.c * Ng)) := by
  refine WP.mono (WP.keepV (by simp [writesV]) (wp_addImm hb fun s4 h4 e4 => wp_addImm hi fun s5 h5 e5 =>
    wp_subImm (by decide) fun s6 h6 e6 => wp_nil (Q := fun t => Only [.x0, .x3, .x11] s t ∧
      t.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * (k + 1)) ∧
      t.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * Ng) - (k + 1)) ⟨((h4.trans h5).trans h6).mono, ?_, ?_, ?_⟩))
    fun t ⟨⟨o, a, b, c⟩, v⟩ => ⟨o, v, a, b, c, by rw [c]; omega_using [hk]⟩
  · rw [h6.get .x0, h5.get .x0, e4, h0, ptr_add, Nat.mul_succ]
  · rw [h6.get .x3, e5, h4.get .x3, h3, coeffAddr, coeffAddr, ptr_add]; congr 2; rw [Nat.mul_succ]; omega_using []
  · have c : (s5.gpr .x11).toNat = 256 / (w.c * Ng) - k := by rw [h5.get .x11, h4.get .x11, h11]
    rw [e6, toNat_sub_n (by rw [c]; simp; omega_using [hk]), c]; simp; omega_using []

/-- The loop of one width. -/
theorem dloop_ok {w : Width} (hw : WOk w) {Ng n : Nat} {K : State → Prop} {setup body : List Instr}
    {s₀ : State} (hn : 256 / (w.c * Ng) = n) (hn0 : 0 < n) (hG : w.c * Ng * n = 256)
    (hset : ∀ s, WP isa (.block setup) s fun t => GFr s t ∧
      (∀ r, r ≠ .v18 → r ≠ .v19 → r ≠ .v20 → r ≠ .v21 → r ≠ .v22 → r ≠ .v23 → t.v r = s.v r) ∧ K t)
    (hK : ∀ s t, t.v = s.v → K s → K t)
    (hstep : ∀ k < n, ∀ s, DInv w Ng K s₀ k s →
      WP isa (.block body) s fun t => DInv w Ng K s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ n)) :
    WP isa (ddLoop w.d n setup body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      PolyIs s'.mem (fP s₀) (decodeDecompress w.d (B w s₀)) := by
  refine WP.seq ?_
  simp only [List.append_assoc]
  have hd := hw.d_le
  have hd' := hw.d_pos
  refine wp_dupW (c := 3329) (by decide) fun s1 g1 v1 l16 =>
    wp_dupW (c := 2 ^ (w.d - 1)) (Nat.pow_lt_pow_right (by decide) (by omega_using [hd])) fun s2 g2 v2 l17 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hset s2) fun s4 ⟨g4, v4, k4⟩ => ?_
  rw [← List.append_nil (movImm .x11 _)]
  refine wp_scalar (movImm_noV _ _) (wp_movImm (is := []) fun t h e =>
    wp_nil (Q := fun t => Only [.x11] s4 t ∧ t.gpr .x11 = BitVec.ofNat 64 n) ⟨h, e⟩) fun s5 ⟨h5, e5⟩ v5 => wp_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x11 → s5.gpr r = s₀.gpr r := fun r h9 h11 => by
    rw [h5.gpr r (by simpa using h11), g4.gpr r h9, g2.gpr r h9, g1.gpr r h9]
  have m5 : s5.mem = s₀.mem := by rw [h5.mem, g4.mem, g2.mem, g1.mem]
  have h0 : DInv w Ng K s₀ 0 s5 := by
    refine ⟨by rw [h5.rd, g4.rd, g2.rd, g1.rd], by rw [h5.wr, g4.wr, g2.wr, g1.wr],
      by rw [h5.sp, g4.sp, g2.sp, g1.sp], ?_, ?_, ?_, ⟨?_, ?_⟩, hK _ _ v5 k4, ?_, ?_⟩
    · rw [g .x0 (by decide) (by decide), Nat.mul_zero, ptr_zero]
    · rw [g .x3 (by decide) (by decide), Nat.mul_zero]; exact (ptr_zero _).symm
    · rw [e5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.div_le_self 256 (w.c * Ng); omega_using [hn, this]), hn,
        Nat.sub_zero]
    · rw [v5, v4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v2 _ (by decide)]; exact l16
    · rw [v5, v4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l17
    · rw [m5, Nat.mul_zero]; exact CoeffsUpTo.zero _
    · rw [m5]; exact Frame.refl _ _
  refine WP.mono (count_loop hn0 (DInv w Ng K s₀) hstep h0) fun s' h => ⟨h.rd, h.wr, h.sp, ?_⟩
  exact (show CoeffsUpTo _ _ 256 _ _ from hG ▸ h.out).polyIs fun _ _ => rfl

end VG.Proof.MlKem.AArch64.DD

end

end

/-!
# ML-KEM on AArch64: storing decompressed coefficients

Two vectors stored as the next eight coefficients of the output (`wp_strq2`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

theorem num1 {w : Width} (hw : w.nb = 1) (s₀ : State) (g : Nat) : num w s₀ g 1 = byte w s₀ g := by
  simp [num, digits, hw]

/-- What a store of coefficients keeps of the state. -/
structure StFr (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  v : t.v = s.v
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem StFr.trans {s t u : State} (h : StFr s t) (h' : StFr t u) : StFr s u :=
  ⟨h'.gpr.trans h.gpr, h'.v.trans h.v, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

/-- `a` and `b` stored at `x3 + o`, coefficients `t … t + 7`. -/
theorem wp_strq2 {s : State} {p : Addr} {m₀ : Mem} {a b : VReg} {o t : Nat} {Gf old : Nat → BitVec 32}
    {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16)
    (ht : t + 8 ≤ 256) (hc : CoeffsUpTo s.mem p t Gf old) (hf : Frame [polyRegion p] m₀ s.mem)
    (ha : ∀ e < 4, vword (s.v a) e = Gf (t + e)) (hb : ∀ e < 4, vword (s.v b) e = Gf (t + 4 + e))
    (k : ∀ s', StFr s s' → CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block (.strq a .x3 o :: .strq b .x3 (o + 16) :: is)) s Q := by
  refine wp_strq (a := coeffAddr p t) ⟨ho.1, by omega_using [ho]⟩ h3 (hw t (by omega_using [ht])) fun s1 h1 => ?_
  refine wp_strq (a := coeffAddr p (t + 4)) ⟨by omega_using [ho], ho.2⟩
    (by rw [h1.gpr, ← ptr_add, h3]; exact coeffAddr_step _ _) (by rw [h1.wr]; exact hw _ (by omega_using [ht]))
    fun s2 h2 => k s2 ⟨by rw [h2.gpr, h1.gpr], by rw [h2.v, h1.v], by rw [h2.rd, h1.rd],
      by rw [h2.wr, h1.wr], by rw [h2.sp, h1.sp]⟩ ?_ ?_
  · rw [h2.mem, h1.v, h1.mem, show t + 8 = t + 4 + 4 by omega_using []]
    exact (hc.write16 (by omega_using [ht]) ha).write16 (by omega_using [ht]) hb
  · rw [h2.mem, h1.mem]
    exact frame16 (frame16 hf (by omega_using [ht]) _) (by omega_using [ht]) _

end VG.Proof.MlKem.AArch64.DD

end

end

/-! ### `MlKem.AArch64.CodecV.DdSplit`, which this module and modules that import it used -/

section

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
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl

/-- The value of `b` bits `m` of two groups of `4 b` bits. -/
abbrev dig (b : Nat) (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 4) / 2 ^ (b * (m % 4)) % 2 ^ b

/-- The words of `v` after TRN1: the low word and the high `2 b` bits of each group. -/
abbrev V2 (b : Nat) (Gv : Nat → Nat) (e : Nat) : Nat :=
  if e % 2 = 0 then Gv (e / 2) % 2 ^ 32 else Gv (e / 2) / 2 ^ (2 * b) % 2 ^ 32

/-- Value `m` of the two groups, as `ddSplit` computes it. -/
abbrev CS (b : Nat) (Gv : Nat → Nat) (m : Nat) : Nat :=
  if m < 4 then (if m % 2 = 0 then V2 b Gv (m / 2) % 2 ^ (2 * b) % 2 ^ b else V2 b Gv (m / 2) % 2 ^ (2 * b) / 2 ^ b)
  else (if (m - 4) % 2 = 0 then V2 b Gv (2 + (m - 4) / 2) % 2 ^ (2 * b) % 2 ^ b
    else V2 b Gv (2 + (m - 4) / 2) % 2 ^ (2 * b) / 2 ^ b)

theorem splitCS {b : Nat} (hb : b = 10 ∨ b = 11) {Gv : Nat → Nat} {m : Nat} (hm : m < 8) :
    CS b Gv m = dig b Gv m := by
  rcases hb with rfl | rfl <;>
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [CS, V2, dig] <;> omega_arith

theorem ddSplit_ok {s : State} {b : Nat} (hb : b = 10 ∨ b = 11) {g : VReg}
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ (2 * b) - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ b - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv)
    {is : List Instr} {Q : State → Prop}
    (g1 : g ≠ .v1 := by decide) (g2 : g ≠ .v2 := by decide)
    (g18 : g ≠ .v18 := by decide) (g19 : g ≠ .v19 := by decide)
    (k : ∀ s', VChg [g, .v1, .v2, .v3] s s' → Lanes (s'.v .v2) (fun e => dig b Gv e) →
      Lanes (s'.v .v3) (fun e => dig b Gv (4 + e)) → WP isa (.block is) s' Q) :
    WP isa (.block (ddSplit b g ++ is)) s Q := by
  have hb22 : 2 * b < 32 := by omega_arith
  have hsh1 : VShiftOp.ok .ushr VArr.d2.esize (2 * b) = true := by
    rcases hb with rfl | rfl <;> decide
  have hsh2 : VShiftOp.ok .ushr VArr.s4.esize b = true := by
    rcases hb with rfl | rfl <;> decide
  unfold ddSplit
  simp only [List.cons_append, List.nil_append]
  refine wp_vop (eval_shift hsh1) fun a1 h1 => wp_vop rfl fun a2 h2 => wp_vop rfl fun a3 h3' =>
    wp_vop (eval_shift hsh2) fun a4 h4 => wp_vop rfl fun a5 h5 => wp_vop rfl fun a6 h6 =>
    wp_vop rfl fun a7 h7 => ?_
  -- the low word and the high `2 b` bits of each group
  have A : ∀ l < 2, (vword (s.v g) (2 * l)).toNat = Gv l % 2 ^ 32 := fun l hl => by
    have w := vdword_words' (s.v g) l
    rw [hG l hl] at w
    have := (vword (s.v g) (2 * l + 1)).isLt
    omega_arith
  have B : ∀ l < 2, (vword (a1.v .v1) (2 * l)).toNat = Gv l / 2 ^ (2 * b) % 2 ^ 32 := fun l hl => by
    have dv : (vdword (a1.v .v1) l).toNat = Gv l / 2 ^ (2 * b) := by
      rw [h1.v, StraightV.vdword_map2 _ _ _ hl]
      simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hG l hl]
    have w := vdword_words' (a1.v .v1) l
    rw [dv] at w
    have := (vword (a1.v .v1) (2 * l)).isLt
    have := (vword (a1.v .v1) (2 * l + 1)).isLt
    omega_arith
  have L2 : Lanes (a2.v g) (V2 b Gv) := fun e he => by
    rw [h2.v, vword_trn1_s4 _ _ he, h1.get g g1]
    simp only [V2]
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [ite_eq_left h, ite_eq_left h, show e = 2 * (e / 2) from by omega_arith, A _ (by omega_arith)]
      congr 2; omega_arith
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), show e - 1 = 2 * (e / 2) from by omega_arith,
        B _ (by omega_arith)]
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
    · exact L5 _ (by omega_arith)
    · exact L4 _ (by omega_arith)
  have L7 : Lanes (a7.v .v3) fun e => CS b Gv (4 + e) := fun e he => by
    rw [h7.v, vword_zip2_s4 _ _ he, h6.get g g2, h6.get .v1 (by decide), h5.get .v1 g1.symm]
    simp only [CS, show ¬ 4 + e < 4 by omega_arith, ite_false, show 4 + e - 4 = e by omega_arith]
    split
    · exact L5 _ (by omega_arith)
    · exact L4 _ (by omega_arith)
  refine k a7 ((((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans h5.chg).trans
    (h6.chg.trans h7.chg)).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hr ⊢
      rcases hr with h | h | h | h | h | h | h <;> simp [h]))
    (L6.congr fun e he => splitCS hb (by omega_arith))
    (L7.congr fun e he => splitCS hb (by omega_arith))

end VG.Proof.MlKem.AArch64.CodecV

end

end

/-!
# ML-KEM on AArch64: an iteration of `dd10Body`

Bytes `20 k … 20 k + 19` of the input, as four groups of 40 bits in doublewords (TBL), to
coefficients `16 k … 16 k + 15` of the output.
-/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/CodecV/Dd10.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: `dd10Half`

Two groups of 40 bits, in the doublewords of a register, split into their eight values of ten
bits (`ddSplit_ok`), decompressed and stored (`dd10Half_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G)

/-- The value of ten bits `m` of two groups of 40 bits. -/
abbrev dig10 (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 4) / 2 ^ (10 * (m % 4)) % 2 ^ 10

theorem dd10Half_ok {s : State} {g : VReg} (hg : g = .v6 ∨ g = .v7) {o : Nat} (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16)
    (hc : DConsts 10 s) (h18 : Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 10 - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 8 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 8, Gf (t + m) = BitVec.ofNat 32 (df 10 (dig10 Gv m)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ g → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd10Half g o ++ is)) s Q := by
  obtain g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  obtain g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  obtain g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  obtain g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  obtain g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  obtain g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  unfold dd10Half
  simp only [List.append_assoc]
  refine ddSplit_ok (b := 10) (.inl rfl) h18 h19 hG g1 g2 g18 g19 fun a7 c7 L6 L7 => ?_
  obtain cs7 : DConsts 10 a7 := hc.chg c7 (by simp [g16.symm]) (by simp [g17.symm])
  obtain dig_lt : ∀ m, dig 10 Gv m < 2 ^ 10 := fun m => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) cs7.q cs7.h (by decide) L6
    fun e _ => dig_lt e) fun b1 ⟨d1, r2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (cs7.chg d1).q (cs7.chg d1).h (by decide)
    (Lanes.chg d1 (by decide) L7) fun e _ => dig_lt _) fun b2 ⟨d2, r3⟩ => ?_
  obtain c := c7.trans (d1.trans d2)
  simp only [List.cons_append, List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ho ht (by rw [c.mem]; exact hcu)
    (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg d2 (by decide) r2) fun e he => by rw [hval e (by omega_using [he])])
    (vword_G r3 fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega_using [he])])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r a b d e => by rw [st.v, c.v r (by simp [a, b, d, e])]) o f

end VG.Proof.MlKem.AArch64.CodecV
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd10Body` besides those of `decV`. -/
abbrev K10 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 10 - 1) ∧
  s.v .v20 = idxVec dd10Idx ∧ s.v .v21 = idxVec dd10IdxHi

theorem dd10Idx_eq : ∀ i < 16, dd10Idx.getD i 255 = if i % 8 < 5 then 5 * (i / 8) + i % 8 else 255 := by
  decide
theorem dd10IdxHi_eq : ∀ i < 16, dd10IdxHi.getD i 255 = if i % 8 < 5 then 10 + 5 * (i / 8) + i % 8 else 255 := by
  decide

/-- TBL at an index past the table. -/
theorem vbyte_tbl2_out {s : State} {n m d : VReg} {i : Nat} (hi : i < 16) {k : Nat}
    (hk : (vbyte (s.v m) i).toNat = k) (hk' : 32 ≤ k) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * 2 then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i = 0 := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_right (by omega_arith)]; rfl

/-- A doubleword from its bytes. -/
theorem dword_of_bytes (x : BitVec 128) (l : Nat) :
    (vdword x l).toNat = (vbyte x (8 * l)).toNat + (vbyte x (8 * l + 1)).toNat * 2 ^ 8 +
      (vbyte x (8 * l + 2)).toNat * 2 ^ 16 + (vbyte x (8 * l + 3)).toNat * 2 ^ 24 +
      (vbyte x (8 * l + 4)).toNat * 2 ^ 32 + (vbyte x (8 * l + 5)).toNat * 2 ^ 40 +
      (vbyte x (8 * l + 6)).toNat * 2 ^ 48 + (vbyte x (8 * l + 7)).toNat * 2 ^ 56 := by
  obtain h0 := toNat_vbyte_dword x (l := l) (b := 0) (by decide)
  obtain h1 := toNat_vbyte_dword x (l := l) (b := 1) (by decide)
  obtain h2 := toNat_vbyte_dword x (l := l) (b := 2) (by decide)
  obtain h3 := toNat_vbyte_dword x (l := l) (b := 3) (by decide)
  obtain h4 := toNat_vbyte_dword x (l := l) (b := 4) (by decide)
  obtain h5 := toNat_vbyte_dword x (l := l) (b := 5) (by decide)
  obtain h6 := toNat_vbyte_dword x (l := l) (b := 6) (by decide)
  obtain h7 := toNat_vbyte_dword x (l := l) (b := 7) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have := (vdword x l).isLt
  omega_arith

/-- A doubleword whose bytes are five values and three zeros. -/
theorem dword5 (x : BitVec 128) (l : Nat) (F : Nat → Nat)
    (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then F b else 0) :
    (vdword x l).toNat = F 0 + F 1 * 2 ^ 8 + F 2 * 2 ^ 16 + F 3 * 2 ^ 24 + F 4 * 2 ^ 32 := by
  obtain hx0 := hx 0 (by decide)
  simp only [Nat.add_zero] at hx0
  rw [dword_of_bytes, hx0, hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide),
    hx 5 (by decide), hx 6 (by decide), hx 7 (by decide)]
  rw [ite_eq_left (show 0 < 5 by decide), ite_eq_left (show 1 < 5 by decide), ite_eq_left (show 2 < 5 by decide),
    ite_eq_left (show 3 < 5 by decide), ite_eq_left (show 4 < 5 by decide), ite_eq_right (show ¬ 5 < 5 by decide),
    ite_eq_right (show ¬ 6 < 5 by decide), ite_eq_right (show ¬ 7 < 5 by decide)]
  omega_arith

/-- The bytes of a group, from its five bytes and three zeros. -/
theorem num5 (s₀ : State) (g : Nat) :
    num width10 s₀ g 5 = byte width10 s₀ (5 * g) + byte width10 s₀ (5 * g + 1) * 2 ^ 8 +
      byte width10 s₀ (5 * g + 2) * 2 ^ 16 + byte width10 s₀ (5 * g + 3) * 2 ^ 24 +
      byte width10 s₀ (5 * g + 4) * 2 ^ 32 := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width10.nb = 5 from rfl, Nat.add_zero]
  omega_arith

/-- Coefficient `16 k + m` of the output for `d = 10`. -/
theorem G10 (s₀ : State) {k m : Nat} (hk : k < 16) (hm : m < 16) :
    DD.G width10 s₀ (16 * k + m) = BitVec.ofNat 32 (df 10 (dig10 (fun l => num width10 s₀ (4 * k + l) 5) m)) := by
  rw [show 16 * k + m = width10.c * (4 * k + m / 4) + m % 4 by simp [width10]; omega_arith,
    G_eq width10_ok s₀ (by simp [width10]; omega_arith) (by simp [width10]; omega_arith)]
  simp only [show width10.d = 10 from rfl, show width10.nb = 5 from rfl, df, dig10]

theorem vbyte_setLane0 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 4) :
    vbyte (setLane x 32 0 w) j = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega_arith,
    show 8 * j + i < 32 by omega_arith, show ¬ 8 * j + i < 0 by omega_arith]
  simp

theorem readW32_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (((m.readW a 32).setWidth 64).setWidth 32).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 4) hj]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Mem.readW, hi, show 8 * j + i < 32 by omega_arith]

theorem step10 {s₀ : State} (hp : Pre width10 s₀) {k : Nat} (hk : k < 16) {s : State}
    (h : DInv width10 4 K10 s₀ k s) :
    WP isa (.block dd10Body) s fun t =>
      DInv width10 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 16) := by
  obtain x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (20 * k) := by
    rw [h.x0, show width10.nb * 4 * k = 20 * k by simp [width10]; try omega_arith]
  unfold dd10Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width10_ok hp (by simp [width10]; omega_arith))
    fun s1 h1 => ?_
  obtain in4 : InRegions (s1.rd ++ s1.wr) (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 4 := by
    rw [h1.rd, h1.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega_arith) (by decide)))
  refine wp_scalar (is := [.ldr .w .x9 .x0 16]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (20 * k + 16))
    (by decide) (by rw [h1.gpr, x0, ptr_add]) in4 fun t o e =>
      wp_nil (Q := fun t => Only [.x9] s1 t ∧ t.gpr .x9 = (s1.mem.readW (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 32).setWidth 64)
      ⟨o, e⟩) fun s2 ⟨o2, e2⟩ v2 => ?_
  refine wp_vop rfl fun s3 h3 => wp_vop rfl fun s4 h4 => wp_vop rfl fun s5 h5 => ?_
  -- the 20 bytes, as a table of two registers
  obtain tab : ∀ i < 20, (if i < 16 then vbyte (s3.v .v4) i else vbyte (s3.v .v5) (i - 16)).toNat =
      byte width10 s₀ (20 * k + i) := fun i hi => by
    by_cases hi' : i < 16
    · rw [ite_eq_left hi', h3.get .v4 (by decide), v2, h1.v]
      exact vbyte_input width10_ok hp h.frame (by simp [width10]; omega_arith) hi'
    · rw [ite_eq_right hi', h3.v, vbyte_setLane0 _ _ (by omega_arith), e2, h1.mem, readW32_byte _ _ (by omega_arith),
        ptr_add, show 20 * k + 16 + (i - 16) = 20 * k + i by omega_arith]
      exact hp.byte_eq h.frame (by simp [width10]; omega_arith) (by decide)
  obtain k20 : s3.v .v20 = idxVec dd10Idx := by
    rw [h3.get .v20 (by decide), v2, h1.get .v20 (by decide)]; exact h.K.2.2.1
  obtain k21 : s4.v .v21 = idxVec dd10IdxHi := by
    rw [h4.get .v21 (by decide), h3.get .v21 (by decide), v2, h1.get .v21 (by decide)]; exact h.K.2.2.2
  -- the groups
  let Gv : Nat → Nat := fun l => num width10 s₀ (4 * k + l) 5
  have lane (x : BitVec 128) (l : Nat) (gb : Nat)
      (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then byte width10 s₀ (5 * gb + b) else 0) :
      (vdword x l).toNat = num width10 s₀ gb 5 := by
    rw [num5]
    exact dword5 x l (fun b => byte width10 s₀ (5 * gb + b)) hx
  obtain D6 : DLanes (s5.v .v6) Gv := fun l hl => lane _ l _ fun b hb => by
    rw [h5.get .v6 (by decide), h4.v]
    obtain hk : (vbyte (s3.v .v20) (8 * l + b)).toNat = dd10Idx.getD (8 * l + b) 255 := by
      rw [k20, toNat_idxVec _ (by decide) (by omega_arith)]
    rw [dd10Idx_eq _ (by omega_arith), show (8 * l + b) % 8 = b by omega_arith, show (8 * l + b) / 8 = l by omega_arith] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega_arith) hk (by omega_arith), show VReg.v4.succ = .v5 from rfl, tab _ (by omega_arith)]
      congr 1; omega_arith
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega_arith) hk (by omega_arith)]; rfl
  obtain D7 : DLanes (s5.v .v7) fun l => Gv (2 + l) := fun l hl => lane _ l _ fun b hb => by
    rw [h5.v]
    obtain hk : (vbyte (s4.v .v21) (8 * l + b)).toNat = dd10IdxHi.getD (8 * l + b) 255 := by
      rw [k21, toNat_idxVec _ (by decide) (by omega_arith)]
    rw [dd10IdxHi_eq _ (by omega_arith), show (8 * l + b) % 8 = b by omega_arith, show (8 * l + b) / 8 = l by omega_arith] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega_arith) hk (by omega_arith), show VReg.v4.succ = .v5 from rfl, h4.get .v4 (by decide),
        h4.get .v5 (by decide), tab _ (by omega_arith)]
      congr 1; omega_arith
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega_arith) hk (by omega_arith)]; rfl
  -- the frame so far
  obtain g5 : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, h4.gpr, h3.gpr, o2.gpr r (by simpa using hr), h1.gpr]
  obtain v5 : ∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → s5.v r = s.v r := fun r a b c d => by
    rw [h5.get r d, h4.get r c, h3.get r b, v2, h1.get r a]
  obtain m5 : s5.mem = s.mem := by rw [h5.mem, h4.mem, h3.mem, o2.mem, h1.mem]
  obtain wr5 : s5.wr = s.wr := by rw [h5.wr, h4.wr, h3.wr, o2.wr, h1.wr]
  obtain cs5 : DConsts 10 s5 := ⟨by rw [v5 .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
    by rw [v5 .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  obtain l18 : Lanes (s5.v .v18) fun _ => 2 ^ 20 - 1 := by
    rw [v5 .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.K.1
  obtain l19 : Lanes (s5.v .v19) fun _ => 2 ^ 10 - 1 := by
    rw [v5 .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1
  obtain x3 : s.gpr .x3 = coeffAddr (fP s₀) (16 * k) := by
    rw [h.x3, show width10.c * 4 * k = 16 * k by simp [width10]; try omega_arith]
  obtain out : CoeffsUpTo s5.mem (fP s₀) (16 * k) (DD.G width10 s₀) (old s₀) := by
    rw [m5, show 16 * k = width10.c * 4 * k by simp [width10]; try omega_arith]; exact h.out
  refine dd10Half_ok (Or.inl rfl) (o := 0) (by decide) cs5 l18 l19 D6
    (fun i hi => by rw [wr5]; exact h.out16 hp hi) (by rw [g5 .x3 (by decide), x3, ptr_zero]) (by omega_arith) out
    (by rw [m5]; exact h.frame) (fun m hm => G10 s₀ hk (by omega_arith)) fun s6 g6 rd6 wr6 sp6 v6 o6 f6 => ?_
  refine dd10Half_ok (Or.inr rfl) (o := 32) (by decide)
    ⟨by rw [v6 .v16 (by decide) (by decide) (by decide) (by decide)]; exact cs5.q,
     by rw [v6 .v17 (by decide) (by decide) (by decide) (by decide)]; exact cs5.h⟩
    (by rw [v6 .v18 (by decide) (by decide) (by decide) (by decide)]; exact l18)
    (by rw [v6 .v19 (by decide) (by decide) (by decide) (by decide)]; exact l19)
    (by rw [v6 .v7 (by decide) (by decide) (by decide) (by decide)]; exact D7)
    (fun i hi => by rw [wr6, wr5]; exact h.out16 hp hi)
    (by rw [g6, g5 .x3 (by decide), x3]; exact coeffAddr_off _ _ 8) (by omega_arith) o6 f6
    (fun m hm => by
      rw [show 16 * k + 8 + m = 16 * k + (8 + m) by omega_arith, G10 s₀ hk (by omega_arith)]
      simp only [dig10]
      rw [show (8 + m) / 4 = 2 + m / 4 by omega_arith, show (8 + m) % 4 = m % 4 by omega_arith])
    fun s7 g7 rd7 wr7 sp7 v7 o7 f7 => ?_
  obtain k4 : k < 256 / (width10.c * 4) := by simp [width10]; omega_arith
  obtain gg : ∀ r, r ≠ .x9 → s7.gpr r = s.gpr r := fun r hr => by rw [g7, g6, g5 r hr]
  refine WP.mono (dtail_ok (w := width10) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  obtain hv : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → u.v r = s.v r :=
    fun r a b c d e f g' => by rw [uv, v7 r g' a b c, v6 r f a b c, v5 r d e f g']
  refine ⟨⟨by rw [o.rd, rd7, rd6, h5.rd, h4.rd, h3.rd, o2.rd, h1.rd, h.rd], by rw [o.wr, wr7, wr6, wr5, h.wr],
    by rw [o.sp, sp7, sp6, h5.sp, h4.sp, h3.sp, o2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [hv .v16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
     by rw [hv .v17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩,
    ⟨by rw [hv .v18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.1,
     by rw [hv .v19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1,
     by rw [hv .v20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.1,
     by rw [hv .v21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.2⟩,
    ?_, by rw [o.mem]; exact f7⟩, by rw [show 256 / (width10.c * 4) = 16 from rfl] at uc; exact uc⟩
  rw [o.mem, show width10.c * 4 * (k + 1) = 16 * k + 8 + 8 by simp [width10]; omega_arith]
  exact o7


end VG.Proof.MlKem.AArch64.DD
