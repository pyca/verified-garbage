module

import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract
import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem1024.Contract
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dword88
meta import VerifiedGarbage.Proof.Framework.AArch64.StraightV
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dword88

/-! ### `MlKem1024.AArch64.CodecV.Dd11Step`, which only this module used -/

section

/-! ### `MlKem1024.AArch64.CodecV.Dd11`, which only this module used -/

section

/-!
# ML-KEM-1024 on AArch64: `dd11Group`

The 11 bytes of a group of 88 bits put in a register by TBL, split into two doublewords of 44 bits
(USHR, SHL, EXT, ORR and ZIP1: the low doubleword keeps bits above the group's low 44, which
`ddSplit` masks off), split into their eight values of 11 bits (`ddSplit_ok`), decompressed and
stored (`dd11Group_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G dword_of_bytes)

/-- The number whose eleven bytes are `B 0 … B 10`. -/
abbrev num11 (B : Nat → Nat) : Nat :=
  B 0 + B 1 * 2 ^ 8 + B 2 * 2 ^ 16 + B 3 * 2 ^ 24 + B 4 * 2 ^ 32 + B 5 * 2 ^ 40 + B 6 * 2 ^ 48 + B 7 * 2 ^ 56 +
    B 8 * 2 ^ 64 + B 9 * 2 ^ 72 + B 10 * 2 ^ 80

theorem dd11Idx_eq (g : Nat) {j : Nat} (hj : j < 16) :
    (dd11Idx g).getD j 255 = if j < 11 then 11 * g + j else 255 := by
  unfold dd11Idx
  by_cases h : j < 11
  · rw [ite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega_arith)]
    rfl

theorem dd11IdxReg_eq {g : Nat} (hg : g < 4) :
    dd11IdxReg g = .v20 ∨ dd11IdxReg g = .v21 ∨ dd11IdxReg g = .v22 ∨ dd11IdxReg g = .v23 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- The values of 11 bits of a group `H` of 88 bits, split as `dd11Group` splits it. -/
theorem dig11_eq (H : Nat) {m : Nat} (hm : m < 8) :
    dig 11 (fun l => if l = 0 then H % 2 ^ 64 else H / 2 ^ 44) m = H / 2 ^ (11 * m) % 2 ^ 11 := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dig, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
      Nat.reducePow, Nat.one_ne_zero, ↓reduceIte, Nat.div_one] <;> omega_arith

theorem dd11Group_ok {s : State} {g : Nat} (hg : g < 4) (hc : DConsts 11 s)
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ 22 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 11 - 1)
    (hidx : s.v (dd11IdxReg g) = idxVec (dd11Idx g))
    {B : Nat → Nat} (hB : ∀ j < 11, (tableByte s.v .v4 (11 * g + j)).toNat = B j)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 (32 * g) = coeffAddr p t) (ht : t + 8 ≤ 256)
    (hcu : CoeffsUpTo s.mem p t Gf old) (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 8, Gf (t + m) = BitVec.ofNat 32 (df 11 (num11 B / 2 ^ (11 * m) % 2 ^ 11)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd11Group g ++ is)) s Q := by
  unfold dd11Group
  simp only [List.append_assoc, List.cons_append]
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s1 h1 => wp_vop (eval_shift (by decide)) fun s2 h2 =>
    wp_vop (eval_shift (by decide)) fun s3 h3' => wp_vop (by simp only [VOp.eval]; rfl) fun s4 h4 =>
    wp_vop rfl fun s5 h5 => wp_vop rfl fun s6 h6 => ?_
  -- the group, in the low 11 bytes of `v7`
  obtain hBl : ∀ j < 11, B j < 2 ^ 8 := fun j hj => by rw [← hB j hj]; exact (tableByte s.v .v4 _).isLt
  obtain r7 : ∀ j < 16, (vbyte (s1.v .v7) j).toNat = if j < 11 then B j else 0 := fun j hj => by
    rw [h1.v]
    obtain hk : (vbyte (s.v (dd11IdxReg g)) j).toNat = if j < 11 then 11 * g + j else 255 := by
      rw [hidx, toNat_idxVec _ (by
        intro x hx; simp only [dd11Idx, List.mem_map, List.mem_range] at hx; omega) hj, dd11Idx_eq g hj]
    by_cases h : j < 11
    · rw [ite_eq_left h] at hk ⊢
      rw [vbyte_tblN hj hk (by omega_arith), hB j h]
    · rw [ite_eq_right h] at hk ⊢
      rw [vbyte_tblN_out hj hk (by omega_arith)]; rfl
  -- the group as its low eight bytes `L` and its high three `Hh`
  obtain b0 := hBl 0 (by decide); have b1 := hBl 1 (by decide); have b2 := hBl 2 (by decide)
  obtain b3 := hBl 3 (by decide); have b4 := hBl 4 (by decide); have b5 := hBl 5 (by decide)
  obtain b6 := hBl 6 (by decide); have b7 := hBl 7 (by decide); have b8 := hBl 8 (by decide)
  obtain b9 := hBl 9 (by decide); have b10 := hBl 10 (by decide)
  generalize hL : B 0 + B 1 * 2 ^ 8 + B 2 * 2 ^ 16 + B 3 * 2 ^ 24 + B 4 * 2 ^ 32 + B 5 * 2 ^ 40 + B 6 * 2 ^ 48 +
    B 7 * 2 ^ 56 = L
  generalize hH : B 8 + B 9 * 2 ^ 8 + B 10 * 2 ^ 16 = Hh
  obtain Llt : L < 2 ^ 64 := by omega_arith
  obtain Hlt : Hh < 2 ^ 24 := by omega_arith
  obtain split : num11 B = L + 2 ^ 64 * Hh := by simp only [num11]; omega_arith
  obtain nlo : num11 B % 2 ^ 64 = L := by
    rw [split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Llt]
  obtain nhi : num11 B / 2 ^ 64 = Hh := by
    rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt Llt, Nat.zero_add]
  obtain lo : (vdword (s1.v .v7) 0).toNat = num11 B % 2 ^ 64 := by
    have := dword_of_bytes (s1.v .v7) 0
    simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [this, r7 0 (by decide), r7 1 (by decide), r7 2 (by decide), r7 3 (by decide), r7 4 (by decide),
      r7 5 (by decide), r7 6 (by decide), r7 7 (by decide), nlo, ← hL]
    simp only [show (0 : Nat) < 11 by decide, show (1 : Nat) < 11 by decide, show (2 : Nat) < 11 by decide,
      show (3 : Nat) < 11 by decide, show (4 : Nat) < 11 by decide, show (5 : Nat) < 11 by decide,
      show (6 : Nat) < 11 by decide, show (7 : Nat) < 11 by decide, ite_true]
  obtain hi : (vdword (s1.v .v7) 1).toNat = num11 B / 2 ^ 64 := by
    have := dword_of_bytes (s1.v .v7) 1
    simp only [Nat.mul_one] at this
    rw [this, r7 8 (by decide), r7 9 (by decide), r7 10 (by decide), r7 11 (by decide), r7 12 (by decide),
      r7 13 (by decide), r7 14 (by decide), r7 15 (by decide), nhi, ← hH]
    simp only [show (8 : Nat) < 11 by decide, show (9 : Nat) < 11 by decide, show (10 : Nat) < 11 by decide,
      show ¬ (11 : Nat) < 11 by decide, show ¬ (12 : Nat) < 11 by decide, show ¬ (13 : Nat) < 11 by decide,
      show ¬ (14 : Nat) < 11 by decide, show ¬ (15 : Nat) < 11 by decide, ite_true, ite_false]
    omega_arith
  -- the high 44 bits in the low doubleword of `v1`
  obtain v7a : s2.v .v7 = s1.v .v7 := h2.get .v7 (by decide)
  obtain d1 : (vdword (s2.v .v1) 0).toNat = num11 B % 2 ^ 64 / 2 ^ 44 := by
    rw [h2.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [lo]
  obtain d2 : (vdword (s4.v .v2) 0).toNat = num11 B / 2 ^ 64 * 2 ^ 20 % 2 ^ 64 := by
    rw [h4.v, vdword_ext8 _ (by decide), h3'.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [v7a, hi]
  obtain d5 : (vdword (s5.v .v1) 0).toNat = num11 B / 2 ^ 44 := by
    rw [h5.v, StraightV.vdword_or, BitVec.toNat_or, h4.get .v1 (by decide), h3'.get .v1 (by decide), d1, d2]
    rw [nlo, nhi, Nat.mod_eq_of_lt (show Hh * 2 ^ 20 < 2 ^ 64 by omega_arith), or_shift (by omega_arith), split,
      show (2 : Nat) ^ 64 = 2 ^ 44 * 2 ^ 20 from by rw [← Nat.pow_add], Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm]
  obtain D : DLanes (s6.v .v7) fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44 := fun l hl => by
    rw [h6.v, eval_zip1_d2]
    rcases (show l = 0 ∨ l = 1 by omega_arith) with rfl | rfl
    · rw [vdword_ofVDwords_0, h5.get .v7 (by decide), h4.get .v7 (by decide), h3'.get .v7 (by decide), v7a, lo]
      simp only [↓reduceIte]
    · rw [vdword_ofVDwords_1, d5]
      simp only [Nat.one_ne_zero, ↓reduceIte]
  obtain c6 : VChg [.v7, .v1, .v2, .v2, .v1, .v7] s s6 :=
    ((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans h5.chg).trans h6.chg
  obtain r18 : Lanes (s6.v .v18) fun _ => 2 ^ (2 * 11) - 1 := Lanes.chg c6 (by decide) h18
  obtain r19 : Lanes (s6.v .v19) fun _ => 2 ^ 11 - 1 := Lanes.chg c6 (by decide) h19
  refine ddSplit_ok (b := 11) (.inr rfl) r18 r19 D (k := fun a7 c7 L2 L3 => ?_)
  obtain cs7 : DConsts 11 a7 := hc.chg (c6.trans c7) (by decide) (by decide)
  -- the values of 11 bits of the group
  obtain dv : ∀ m < 8, dig 11 (fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44) m =
      num11 B / 2 ^ (11 * m) % 2 ^ 11 := fun m hm => dig11_eq _ hm
  obtain dlt : ∀ m, dig 11 (fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44) m < 2 ^ 11 :=
    fun m => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) cs7.q cs7.h (by decide) L2
    fun e _ => dlt e) fun b1 ⟨e1, r2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (cs7.chg e1).q (cs7.chg e1).h (by decide)
    (Lanes.chg e1 (by decide) L3) fun e _ => dlt _) fun b2 ⟨e2, r3⟩ => ?_
  obtain c := (c6.trans c7).trans (e1.trans e2)
  simp only [List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ⟨by omega_arith, by omega_arith⟩ ht
    (by rw [c.mem]; exact hcu) (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg e2 (by decide) r2) fun e he => by rw [hval e (by omega_arith), dv e (by omega_arith)])
    (vword_G r3 fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega_arith), dv (4 + e) (by omega_arith)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r a b d e => by rw [st.v, c.v r (by simp [a, b, d, e])]) o f

end VG.Proof.MlKem1024.AArch64.CodecV

end

end


/-!
# ML-KEM-1024 on AArch64: an iteration of `dd11Body`

Bytes `44 k … 44 k + 43` of the input, in three registers (two loads of 16 bytes, a doubleword and a
word), to coefficients `32 k … 32 k + 31` of the output, a group of 88 bits at a time
(`dd11Group_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd11Body` besides those of `decV`. -/
abbrev K11 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 22 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 11 - 1) ∧
  ∀ g < 4, s.v (dd11IdxReg g) = idxVec (dd11Idx g)

theorem vbyte_setLane64_0 (x : BitVec 128) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    vbyte (setLane x 64 0 w) j = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega_arith,
    show 8 * j + i < 64 by omega_arith, show ¬ 8 * j + i < 0 by omega_arith]
  simp

theorem vbyte_setLane32_2 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 2 w) j = if 8 ≤ j ∧ j < 12 then w.extractLsb' (8 * (j - 8)) 8 else vbyte x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : 8 ≤ j ∧ j < 12
  · rw [ite_eq_left h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, show 8 * j + i < 128 by omega_arith, show ¬ 8 * j + i < 32 * 2 by omega_arith,
      show 8 * j + i - 32 * 2 = 8 * (j - 8) + i by omega_arith, show 8 * (j - 8) + i < 32 by omega_arith,
      show 8 * (j - 8) + i < 128 by omega_arith]
    simp
  · rw [ite_eq_right h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, show 8 * j + i < 128 by omega_arith]
    by_cases h' : 8 * j + i < 32 * 2
    · simp [h']
    · have : ¬ 8 * j + i - 32 * 2 < 32 := by omega_arith
      simp [h', this, BitVec.getLsbD_of_ge w (8 * j + i - 32 * 2) (by omega_arith)]

/-- The bytes of a group, from its 11 bytes. -/
theorem num11_eq (s₀ : State) (g : Nat) :
    num width11 s₀ g 11 = num11 fun j => byte width11 s₀ (11 * g + j) := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ,
    num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width11.nb = 11 from rfl, Nat.add_zero, num11]
  omega_arith

/-- Coefficient `32 k + 8 g + m` of the output for `d = 11`. -/
theorem G11 (s₀ : State) {k g m : Nat} (hk : k < 8) (hg : g < 4) (hm : m < 8) :
    DD.G width11 s₀ (32 * k + 8 * g + m) =
      BitVec.ofNat 32 (df 11 (num11 (fun j => byte width11 s₀ (11 * (4 * k + g) + j)) / 2 ^ (11 * m) % 2 ^ 11)) := by
  rw [show 32 * k + 8 * g + m = width11.c * (4 * k + g) + m by simp [width11]; omega_arith,
    G_eq width11_ok s₀ (by simp [width11]; omega_arith) (by simp [width11]; omega_arith), ← num11_eq]
  simp only [show width11.d = 11 from rfl, show width11.nb = 11 from rfl, df]

theorem tableByte_frame {s u : State} (hu : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s.v r)
    {i : Nat} (hi : i < 48) : tableByte u.v .v4 i = tableByte s.v .v4 i := by
  unfold tableByte
  rcases (show i / 16 = 0 ∨ i / 16 = 1 ∨ i / 16 = 2 by omega_arith) with h | h | h <;> rw [h] <;>
    exact congrArg (fun x => vbyte x _) (hu _ (by decide) (by decide) (by decide) (by decide))

theorem step11 {s₀ : State} (hp : Pre width11 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width11 4 K11 s₀ k s) :
    WP isa (.block dd11Body) s fun t =>
      DInv width11 4 K11 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  obtain x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (44 * k) := by
    rw [h.x0, show width11.nb * 4 * k = 44 * k by simp [width11]; try omega_arith]
  obtain inr : ∀ o n, o + n ≤ 44 → InRegions (s.rd ++ s.wr) (bP s₀ + BitVec.ofNat 64 (44 * k + o)) n := fun o n hon => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width11]; omega_arith) (by decide)))
  unfold dd11Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width11_ok hp (by simp [width11]; omega_arith))
    fun s1 h1 => ?_
  refine wp_ldrq (a := bP s₀ + BitVec.ofNat 64 (44 * k + 16)) (by decide) (by rw [h1.gpr, x0, ptr_add])
    (by rw [h1.rd, h1.wr]; exact inr 16 16 (by decide)) fun s2 h2 => ?_
  refine wp_scalar (is := [.ldr .x .x9 .x0 32]) (by decide) (wp_ldrx (a := bP s₀ + BitVec.ofNat 64 (44 * k + 32))
    (by decide) (by rw [h2.gpr, h1.gpr, x0, ptr_add]) (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact inr 32 8 (by decide))
    fun t o e => wp_nil (Q := fun t => Only [.x9] s2 t ∧ t.gpr .x9 = s2.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 64)
      ⟨o, e⟩) fun s3 ⟨o3, e3⟩ v3 => ?_
  refine wp_vop rfl fun s4 h4 => ?_
  refine wp_scalar (is := [.ldr .w .x9 .x0 40]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (44 * k + 40))
    (by decide) (by rw [h4.gpr, o3.gpr .x0 (by decide), h2.gpr, h1.gpr, x0, ptr_add])
    (by rw [h4.rd, h4.wr, o3.rd, o3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact inr 40 4 (by decide))
    fun t o e => wp_nil (Q := fun t => Only [.x9] s4 t ∧
      t.gpr .x9 = (s4.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 40)) 32).setWidth 64) ⟨o, e⟩)
    fun s5 ⟨o5, e5⟩ v5 => ?_
  refine wp_vop rfl fun s6 h6 => ?_
  obtain m6 : s6.mem = s.mem := by rw [h6.mem, o5.mem, h4.mem, o3.mem, h2.mem, h1.mem]
  -- the 44 bytes, as a table of three registers
  obtain tab : ∀ i < 44, (tableByte s6.v .v4 i).toNat = byte width11 s₀ (44 * k + i) := fun i hi => by
    unfold tableByte
    rcases (show i / 16 = 0 ∨ i / 16 = 1 ∨ i / 16 = 2 by omega_arith) with q | q | q <;> rw [q]
    · rw [show Nat.repeat VReg.succ 0 VReg.v4 = .v4 from rfl, h6.get .v4 (by decide), v5, h4.get .v4 (by decide),
        v3, h2.get .v4 (by decide), h1.v]
      exact vbyte_input width11_ok hp h.frame (by simp [width11]; omega_arith) (by omega_arith) |>.trans
        (by rw [show i % 16 = i by omega_arith])
    · rw [show Nat.repeat VReg.succ 1 VReg.v4 = .v5 from rfl, h6.get .v5 (by decide), v5, h4.get .v5 (by decide),
        v3, h2.v, h1.mem]
      rw [vbyte_input width11_ok hp h.frame (o := 44 * k + 16) (by simp [width11]; omega_arith) (by omega_arith)]
      congr 1; omega_arith
    · rw [show Nat.repeat VReg.succ 2 VReg.v4 = .v6 from rfl, h6.v, vbyte_setLane32_2 _ _ (by omega_arith)]
      by_cases hb : 8 ≤ i % 16 ∧ i % 16 < 12
      · rw [ite_eq_left hb, e5, h4.mem, o3.mem, h2.mem, h1.mem, readW32_byte _ _ (by omega_arith), ptr_add,
          show 44 * k + 40 + (i % 16 - 8) = 44 * k + i by omega_arith]
        exact hp.byte_eq h.frame (by simp [width11]; omega_arith) (by decide)
      · rw [ite_eq_right hb, v5, h4.v, vbyte_setLane64_0 _ _ (by omega_arith), e3, h2.mem, h1.mem]
        rw [show (s.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 64) =
          s.mem.read (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 8 from rfl, Mem.extractLsb'_read _ _ (by omega_arith),
          ptr_add, show 44 * k + 32 + i % 16 = 44 * k + i by omega_arith]
        exact hp.byte_eq h.frame (by simp [width11]; omega_arith) (by decide)
  -- the frame so far
  obtain g6 : ∀ r, r ≠ .x9 → s6.gpr r = s.gpr r := fun r hr => by
    rw [h6.gpr, o5.gpr r (by simpa using hr), h4.gpr, o3.gpr r (by simpa using hr), h2.gpr, h1.gpr]
  obtain v6 : ∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → s6.v r = s.v r := fun r a b c => by
    rw [h6.get r c, v5, h4.get r c, v3, h2.get r b, h1.get r a]
  obtain wr6 : s6.wr = s.wr := by rw [h6.wr, o5.wr, h4.wr, o3.wr, h2.wr, h1.wr]
  obtain x3 : s.gpr .x3 = coeffAddr (fP s₀) (32 * k) := by
    rw [h.x3, show width11.c * 4 * k = 32 * k by simp [width11]; try omega_arith]
  obtain out : CoeffsUpTo s6.mem (fP s₀) (32 * k) (DD.G width11 s₀) (old s₀) := by
    rw [m6, show 32 * k = width11.c * 4 * k by simp [width11]; try omega_arith]; exact h.out
  -- what the groups keep
  obtain keep : ∀ u : State, (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s6.v r) →
      DConsts 11 u ∧ (Lanes (u.v .v18) fun _ => 2 ^ 22 - 1) ∧ (Lanes (u.v .v19) fun _ => 2 ^ 11 - 1) ∧
      (∀ g < 4, u.v (dd11IdxReg g) = idxVec (dd11Idx g)) ∧
      ∀ g < 4, ∀ j < 11, (tableByte u.v .v4 (11 * g + j)).toNat = byte width11 s₀ (11 * (4 * k + g) + j) := by
    intro u hu
    obtain hr : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → u.v r = s.v r :=
      fun r a b c d e f g' => by rw [hu r a b c g', v6 r d e f]
    obtain q : ∀ r, r ∉ [VReg.v1, .v2, .v3, .v4, .v5, .v6, .v7] → u.v r = s.v r := fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨a, b, c, d, e, f, g'⟩ := hr'
      exact hr r a b c d e f g'
    refine ⟨⟨(q .v16 (by decide)).symm ▸ h.cs.q, (q .v17 (by decide)).symm ▸ h.cs.h⟩,
      (q .v18 (by decide)).symm ▸ h.K.1, (q .v19 (by decide)).symm ▸ h.K.2.1,
      fun g hg => ?_, fun g hg j hj => ?_⟩
    · rcases dd11IdxReg_eq hg with e | e | e | e <;> rw [e] <;>
        rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← e] <;>
        exact h.K.2.2 g hg
    · rw [tableByte_frame hu (by omega_arith), tab _ (by omega_arith), show 44 * k + (11 * g + j) = 11 * (4 * k + g) + j by omega_arith]
  obtain hu6 : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → s6.v r = s6.v r := fun _ _ _ _ _ => rfl
  -- the four groups
  obtain grp : ∀ (g : Nat) (u : State), g < 4 → (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s6.v r) →
      u.gpr = s6.gpr → u.wr = s.wr → CoeffsUpTo u.mem (fP s₀) (32 * k + 8 * g) (DD.G width11 s₀) (old s₀) →
      Frame [polyRegion (fP s₀)] s₀.mem u.mem → ∀ (is : List Instr) (Q : State → Prop),
      (∀ u', u'.gpr = u.gpr → u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp →
        (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u'.v r = u.v r) →
        CoeffsUpTo u'.mem (fP s₀) (32 * k + 8 * g + 8) (DD.G width11 s₀) (old s₀) →
        Frame [polyRegion (fP s₀)] s₀.mem u'.mem → WP isa (.block is) u' Q) →
      WP isa (.block (dd11Group g ++ is)) u Q := by
    intro g u hg hu gu wu cu fu is Q kk
    obtain ⟨c, l18, l19, idx, tb⟩ := keep u hu
    exact dd11Group_ok hg c l18 l19 (idx g hg) (B := fun j => byte width11 s₀ (11 * (4 * k + g) + j)) (tb g hg)
      (fun i hi => by rw [wu]; exact h.out16 hp hi)
      (by rw [gu, g6 .x3 (by decide), x3, show 32 * g = 4 * (8 * g) by omega_arith, coeffAddr_off]) (by omega_arith) cu fu
      (fun m hm => G11 s₀ hk hg hm) kk
  refine grp 0 s6 (by decide) hu6 rfl wr6 (by rw [show 32 * k + 8 * 0 = 32 * k by omega_arith]; exact out)
    (by rw [m6]; exact h.frame) _ _ fun u1 g1 rd1 wr1 sp1 v1 o1 f1 => ?_
  refine grp 1 u1 (by decide) (fun r a b c d => by rw [v1 r a b c d]) (by rw [g1]) (by rw [wr1, wr6])
    (by rw [show 32 * k + 8 * 1 = 32 * k + 8 * 0 + 8 by omega_arith]; exact o1) f1 _ _
    fun u2 g2 rd2 wr2 sp2 v2 o2 f2 => ?_
  refine grp 2 u2 (by decide) (fun r a b c d => by rw [v2 r a b c d, v1 r a b c d]) (by rw [g2, g1])
    (by rw [wr2, wr1, wr6]) (by rw [show 32 * k + 8 * 2 = 32 * k + 8 * 1 + 8 by omega_arith]; exact o2) f2 _ _
    fun u3 g3 rd3 wr3 sp3 v3' o3' f3 => ?_
  refine grp 3 u3 (by decide) (fun r a b c d => by rw [v3' r a b c d, v2 r a b c d, v1 r a b c d])
    (by rw [g3, g2, g1]) (by rw [wr3, wr2, wr1, wr6])
    (by rw [show 32 * k + 8 * 3 = 32 * k + 8 * 2 + 8 by omega_arith]; exact o3') f3 _ _
    fun u4 g4 rd4 wr4 sp4 v4 o4 f4 => ?_
  obtain k4 : k < 256 / (width11.c * 4) := by simp [width11]; omega_arith
  obtain gg : ∀ r, r ≠ .x9 → u4.gpr r = s.gpr r := fun r hr => by rw [g4, g3, g2, g1, g6 r hr]
  refine WP.mono (dtail_ok (w := width11) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  obtain ⟨c, l18, l19, idx, -⟩ := keep u4 fun r a b d e => by rw [v4 r a b d e, v3' r a b d e, v2 r a b d e,
    v1 r a b d e]
  refine ⟨⟨by rw [o.rd, rd4, rd3, rd2, rd1, h6.rd, o5.rd, h4.rd, o3.rd, h2.rd, h1.rd, h.rd],
    by rw [o.wr, wr4, wr3, wr2, wr1, wr6, h.wr],
    by rw [o.sp, sp4, sp3, sp2, sp1, h6.sp, o5.sp, h4.sp, o3.sp, h2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [uv]; exact c.q, by rw [uv]; exact c.h⟩,
    ⟨by rw [uv]; exact l18, by rw [uv]; exact l19, fun g hg => by rw [uv]; exact idx g hg⟩,
    ?_, by rw [o.mem]; exact f4⟩, by rw [show 256 / (width11.c * 4) = 8 from rfl] at uc; exact uc⟩
  rw [o.mem, show width11.c * 4 * (k + 1) = 32 * k + 8 * 3 + 8 by simp [width11]; omega_arith]
  exact o4

end VG.Proof.MlKem1024.AArch64.DD

end

end

/-! ### `MlKem1024.AArch64.CodecV.Dd5Step`, which only this module used -/

section

/-! ### `MlKem1024.AArch64.CodecV.Dd5`, which only this module used -/

section

/-!
# ML-KEM-1024 on AArch64: `dd5Half`

Two groups of 40 bits, in the doublewords of a register, split into their eight values of ten bits
(`ddSplit_ok`), each split into two values of five bits (`dd5Quarter_ok`: USHR, AND, ZIP1 and ZIP2),
decompressed and stored (`dd5Half_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G)

/-- The value of five bits `m` of two groups of 40 bits. -/
abbrev dig5 (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 8) / 2 ^ (5 * (m % 8)) % 2 ^ 5

/-- The values of five bits of four values `P` of ten bits, in order. -/
abbrev pair5 (P : Nat → Nat) (i : Nat) : Nat := P (i / 2) / 2 ^ (5 * (i % 2)) % 2 ^ 5

theorem dd5Quarter_ok {s : State} {a : VReg} (ha : a = .v2 ∨ a = .v3) {o : Nat}
    (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16) (hc : DConsts 5 s) (h22 : Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)
    {P : Nat → Nat} (hP : Lanes (s.v a) P) (hPl : ∀ e < 4, P e < 2 ^ 10)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 8 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ i < 8, Gf (t + i) = BitVec.ofNat 32 (df 5 (pair5 P i)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ a → r ≠ .v0 → r ≠ .v1 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd5Quarter a o ++ is)) s Q := by
  obtain a0 : a ≠ .v0 := by rcases ha with rfl | rfl <;> decide
  obtain a1 : a ≠ .v1 := by rcases ha with rfl | rfl <;> decide
  obtain a16 : a ≠ .v16 := by rcases ha with rfl | rfl <;> decide
  obtain a17 : a ≠ .v17 := by rcases ha with rfl | rfl <;> decide
  obtain a22 : a ≠ .v22 := by rcases ha with rfl | rfl <;> decide
  unfold dd5Quarter
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine wp_vop (eval_shift (by decide)) fun s1 h1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3' =>
    wp_vop rfl fun s4 h4 => wp_nil ?_
  obtain L1 : Lanes (s1.v .v1) fun e => P e / 2 ^ 5 := by rw [h1.v]; exact lanes_ushr hP 5 _
  obtain L2 : Lanes (s2.v a) fun e => P e % 2 ^ 5 := by
    rw [h2.v]
    exact lanes_mask (lanes_get h1 a1 hP) (by rw [h1.get .v22 (by decide)]; exact h22)
  -- the values in order: `pair5 P i` for `i < 4` in `v0`, `4 ≤ i < 8` in `a`
  obtain hi : ∀ i < 8, (if i % 2 = 0 then P (i / 2) % 2 ^ 5 else P (i / 2) / 2 ^ 5) = pair5 P i := fun i hi8 => by
    have := hPl (i / 2) (by omega_arith)
    simp only [pair5]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [ite_eq_left h, h, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · rw [ite_eq_right (by omega_arith), h, Nat.mul_one]; omega_arith
  obtain L3 : Lanes (s3.v .v0) fun e => pair5 P e := fun e he => by
    rw [h3'.v, vword_zip1_s4' _ _ he]
    show _ = pair5 P e
    rw [← hi e (by omega_arith)]
    split
    · exact L2 _ (by omega_arith)
    · rw [h2.get .v1 (Ne.symm a1)]; exact L1 _ (by omega_arith)
  obtain L4 : Lanes (s4.v a) fun e => pair5 P (4 + e) := fun e he => by
    rw [h4.v, vword_zip2_s4 _ _ he]
    show _ = pair5 P (4 + e)
    rw [← hi (4 + e) (by omega_arith), h3'.get a a0, h3'.get .v1 (by decide),
      h2.get .v1 (Ne.symm a1), show (4 + e) / 2 = 2 + e / 2 by omega_arith, show (4 + e) % 2 = e % 2 by omega_arith]
    split
    · exact L2 _ (by omega_arith)
    · exact L1 _ (by omega_arith)
  obtain c4 : VChg [.v1, a, .v0, a] s s4 := ((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg
  obtain cs4 : DConsts 5 s4 := hc.chg c4 (by simp [Ne.symm a16]) (by simp [Ne.symm a17])
  obtain plt : ∀ i, pair5 P i < 2 ^ 5 := fun i => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v0) (by decide) (by decide) cs4.q cs4.h (by decide)
    (Lanes.chg h4.chg (by simp [Ne.symm a0]) L3)
    fun e _ => plt e) fun b1 ⟨d1, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := a) (by decide) (by decide) (cs4.chg d1).q (cs4.chg d1).h a17
    (Lanes.chg d1 (by simp [a0]) L4) fun e _ => plt _) fun b2 ⟨d2, ra⟩ => ?_
  obtain c := c4.trans (d1.trans d2)
  simp only [List.cons_append, List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ho ht (by rw [c.mem]; exact hcu)
    (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg d2 (by simp [Ne.symm a0]) r0) fun e he => by rw [hval e (by omega_arith)])
    (vword_G ra fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega_arith)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r x y z => by rw [st.v, c.v r (by simp [x, y, z])]) o f

theorem dd5Half_ok {s : State} {g : VReg} (hg : g = .v6 ∨ g = .v7) {o : Nat}
    (ho : o % 16 = 0 ∧ o + 48 < 4096 * 16) (hc : DConsts 5 s)
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 10 - 1)
    (h22 : Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 16 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 16, Gf (t + m) = BitVec.ofNat 32 (df 5 (dig5 Gv m)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ g → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 16) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd5Half g o ++ is)) s Q := by
  obtain g0 : g ≠ .v0 := by rcases hg with rfl | rfl <;> decide
  obtain g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  obtain g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  obtain g3 : g ≠ .v3 := by rcases hg with rfl | rfl <;> decide
  obtain g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  obtain g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  obtain g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  obtain g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  obtain g22 : g ≠ .v22 := by rcases hg with rfl | rfl <;> decide
  unfold dd5Half
  simp only [List.append_assoc]
  refine ddSplit_ok (b := 10) (.inl rfl) h18 h19 hG g1 g2 g18 g19 fun a7 c7 L2 L3 => ?_
  obtain cs7 : DConsts 5 a7 := hc.chg c7 (by simp [g16.symm]) (by simp [g17.symm])
  obtain l22 : Lanes (a7.v .v22) fun _ => 2 ^ 5 - 1 := Lanes.chg c7 (by simp [g22.symm]) h22
  obtain dlt : ∀ m, dig 10 Gv m < 2 ^ 10 := fun m => Nat.mod_lt _ (by decide)
  -- the values of five bits of the values of ten bits
  obtain pq : ∀ (j : Nat) (X : Nat), j < 8 →
      (X / 2 ^ (10 * (j / 2)) % 2 ^ 10) / 2 ^ (5 * (j % 2)) % 2 ^ 5 = X / 2 ^ (5 * j) % 2 ^ 5 := by
    intro j X hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_arith) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega_arith
  refine dd5Quarter_ok (a := .v2) (.inl rfl) (o := o) ⟨ho.1, by omega_arith⟩ cs7 l22 L2 (fun e _ => dlt e)
    (by rw [c7.wr]; exact hw) (by rw [c7.gpr]; exact h3) (by omega_arith) (by rw [c7.mem]; exact hcu)
    (by rw [c7.mem]; exact hf)
    (fun i hi => by
      rw [hval i (by omega_arith)]
      simp only [pair5, dig, dig5]
      rw [show i / 2 / 4 = 0 by omega_arith, show i / 2 % 4 = i / 2 by omega_arith, show i / 8 = 0 by omega_arith,
        show i % 8 = i by omega_arith, pq i _ hi])
    fun s1 g1' rd1 wr1 sp1 v1 o1 f1 => ?_
  refine dd5Quarter_ok (a := .v3) (.inr rfl) (o := o + 32) ⟨by omega_arith, by omega_arith⟩
    ⟨by rw [v1 .v16 (by decide) (by decide) (by decide)]; exact cs7.q,
     by rw [v1 .v17 (by decide) (by decide) (by decide)]; exact cs7.h⟩
    (by rw [v1 .v22 (by decide) (by decide) (by decide)]; exact l22)
    (by rw [v1 .v3 (by decide) (by decide) (by decide)]; exact L3) (fun e _ => dlt _)
    (by rw [wr1, c7.wr]; exact hw)
    (by rw [g1', c7.gpr, ← ptr_add, h3]; exact coeffAddr_off _ _ 8)
    (by omega_arith) o1 f1
    (fun i hi => by
      rw [show t + 8 + i = t + (8 + i) by omega_arith, hval (8 + i) (by omega_arith)]
      simp only [pair5, dig, dig5]
      rw [show (4 + i / 2) / 4 = 1 by omega_arith, show (4 + i / 2) % 4 = i / 2 by omega_arith, show (8 + i) / 8 = 1 by omega_arith,
        show (8 + i) % 8 = i by omega_arith, pq i _ hi])
    fun s2 g2' rd2 wr2 sp2 v2 o2 f2 => ?_
  exact k s2 (by rw [g2', g1', c7.gpr]) (by rw [rd2, rd1, c7.rd]) (by rw [wr2, wr1, c7.wr])
    (by rw [sp2, sp1, c7.sp]) (fun r a b c d e => by
      rw [v2 r e b c, v1 r d b c, c7.v r (by simp [a, c, d, e])])
    (by rw [show t + 16 = t + 8 + 8 by omega_arith]; exact o2) f2

end VG.Proof.MlKem1024.AArch64.CodecV

end

end


/-!
# ML-KEM-1024 on AArch64: an iteration of `dd5Body`

Bytes `20 k … 20 k + 19` of the input, as four groups of 40 bits in doublewords (TBL, as for
`d = 10`), to coefficients `32 k … 32 k + 31` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd5Body` besides those of `decV`. -/
abbrev K5 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 10 - 1) ∧
  s.v .v20 = idxVec dd10Idx ∧ s.v .v21 = idxVec dd10IdxHi ∧ (Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)

/-- The bytes of a group, from its five bytes. -/
theorem num5' (s₀ : State) (g : Nat) :
    num width5 s₀ g 5 = byte width5 s₀ (5 * g) + byte width5 s₀ (5 * g + 1) * 2 ^ 8 +
      byte width5 s₀ (5 * g + 2) * 2 ^ 16 + byte width5 s₀ (5 * g + 3) * 2 ^ 24 +
      byte width5 s₀ (5 * g + 4) * 2 ^ 32 := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width5.nb = 5 from rfl, Nat.add_zero]
  omega_using []

/-- Coefficient `32 k + m` of the output for `d = 5`. -/
theorem G5 (s₀ : State) {k m : Nat} (hk : k < 8) (hm : m < 32) :
    DD.G width5 s₀ (32 * k + m) = BitVec.ofNat 32 (df 5 (dig5 (fun l => num width5 s₀ (4 * k + l) 5) m)) := by
  rw [show 32 * k + m = width5.c * (4 * k + m / 8) + m % 8 by simp [width5]; omega_using [],
    G_eq width5_ok s₀ (by simp [width5]; omega_using [hk, hm]) (by simp [width5]; omega_using [])]
  simp only [show width5.d = 5 from rfl, show width5.nb = 5 from rfl, df, dig5]

theorem step5 {s₀ : State} (hp : Pre width5 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width5 4 K5 s₀ k s) :
    WP isa (.block dd5Body) s fun t =>
      DInv width5 4 K5 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  obtain x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (20 * k) := by
    rw [h.x0, show width5.nb * 4 * k = 20 * k by simp [width5]; try omega_arith]
  unfold dd5Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width5_ok hp (by simp [width5]; omega_arith))
    fun s1 h1 => ?_
  obtain in4 : InRegions (s1.rd ++ s1.wr) (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 4 := by
    rw [h1.rd, h1.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega_arith) (by decide)))
  refine wp_scalar (is := [.ldr .w .x9 .x0 16]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (20 * k + 16))
    (by decide) (by rw [h1.gpr, x0, ptr_add]) in4 fun t o e =>
      wp_nil (Q := fun t => Only [.x9] s1 t ∧ t.gpr .x9 = (s1.mem.readW (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 32).setWidth 64)
      ⟨o, e⟩) fun s2 ⟨o2, e2⟩ v2 => ?_
  refine wp_vop rfl fun s3 h3 => wp_vop rfl fun s4 h4 => wp_vop rfl fun s5 h5 => ?_
  -- the 20 bytes, as a table of two registers
  obtain tab : ∀ i < 20, (if i < 16 then vbyte (s3.v .v4) i else vbyte (s3.v .v5) (i - 16)).toNat =
      byte width5 s₀ (20 * k + i) := fun i hi => by
    by_cases hi' : i < 16
    · rw [ite_eq_left hi', h3.get .v4 (by decide), v2, h1.v]
      exact vbyte_input width5_ok hp h.frame (by simp [width5]; omega_arith) hi'
    · rw [ite_eq_right hi', h3.v, vbyte_setLane0 _ _ (by omega_arith), e2, h1.mem, readW32_byte _ _ (by omega_arith),
        ptr_add, show 20 * k + 16 + (i - 16) = 20 * k + i by omega_arith]
      exact hp.byte_eq h.frame (by simp [width5]; omega_arith) (by decide)
  obtain k20 : s3.v .v20 = idxVec dd10Idx := by
    rw [h3.get .v20 (by decide), v2, h1.get .v20 (by decide)]; exact h.K.2.2.1
  obtain k21 : s4.v .v21 = idxVec dd10IdxHi := by
    rw [h4.get .v21 (by decide), h3.get .v21 (by decide), v2, h1.get .v21 (by decide)]; exact h.K.2.2.2.1
  -- the groups
  let Gv : Nat → Nat := fun l => num width5 s₀ (4 * k + l) 5
  have lane (x : BitVec 128) (l : Nat) (gb : Nat)
      (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then byte width5 s₀ (5 * gb + b) else 0) :
      (vdword x l).toNat = num width5 s₀ gb 5 := by
    rw [num5']
    exact dword5 x l (fun b => byte width5 s₀ (5 * gb + b)) hx
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
  obtain cs5 : DConsts 5 s5 := ⟨by rw [v5 .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
    by rw [v5 .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  obtain l18 : Lanes (s5.v .v18) fun _ => 2 ^ 20 - 1 := by
    rw [v5 .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.K.1
  obtain l19 : Lanes (s5.v .v19) fun _ => 2 ^ 10 - 1 := by
    rw [v5 .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1
  obtain l22 : Lanes (s5.v .v22) fun _ => 2 ^ 5 - 1 := by
    rw [v5 .v22 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.2.2
  obtain x3 : s.gpr .x3 = coeffAddr (fP s₀) (32 * k) := by
    rw [h.x3, show width5.c * 4 * k = 32 * k by simp [width5]; try omega_arith]
  obtain out : CoeffsUpTo s5.mem (fP s₀) (32 * k) (DD.G width5 s₀) (old s₀) := by
    rw [m5, show 32 * k = width5.c * 4 * k by simp [width5]; try omega_arith]; exact h.out
  refine dd5Half_ok (Or.inl rfl) (o := 0) (by decide) cs5 l18 l19 l22 D6
    (fun i hi => by rw [wr5]; exact h.out16 hp hi) (by rw [g5 .x3 (by decide), x3, ptr_zero]) (by omega_arith) out
    (by rw [m5]; exact h.frame) (fun m hm => G5 s₀ hk (by omega_arith)) fun s6 g6 rd6 wr6 sp6 v6 o6 f6 => ?_
  obtain v6' : ∀ r : VReg, r ≠ .v6 → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 →
      s6.v r = s.v r := fun r a b c d e f g' i => by rw [v6 r a b c d e, v5 r f g' a i]
  refine dd5Half_ok (Or.inr rfl) (o := 64) (by decide)
    ⟨by rw [v6 .v16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.q,
     by rw [v6 .v17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.h⟩
    (by rw [v6 .v18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l18)
    (by rw [v6 .v19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l19)
    (by rw [v6 .v22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l22)
    (by rw [v6 .v7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact D7)
    (fun i hi => by rw [wr6, wr5]; exact h.out16 hp hi)
    (by rw [g6, g5 .x3 (by decide), x3]; exact coeffAddr_off _ _ 16) (by omega_arith) o6 f6
    (fun m hm => by
      rw [show 32 * k + 16 + m = 32 * k + (16 + m) by omega_arith, G5 s₀ hk (by omega_arith)]
      simp only [dig5]
      rw [show (16 + m) / 8 = 2 + m / 8 by omega_arith, show (16 + m) % 8 = m % 8 by omega_arith])
    fun s7 g7 rd7 wr7 sp7 v7 o7 f7 => ?_
  obtain k4 : k < 256 / (width5.c * 4) := by simp [width5]; omega_arith
  obtain gg : ∀ r, r ≠ .x9 → s7.gpr r = s.gpr r := fun r hr => by rw [g7, g6, g5 r hr]
  refine WP.mono (dtail_ok (w := width5) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  obtain hv : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7] → u.v r = s.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hr
    rw [uv, v7 r a7 a0 a1 a2 a3, v6' r a6 a0 a1 a2 a3 a4 a5 a7]
  refine ⟨⟨by rw [o.rd, rd7, rd6, h5.rd, h4.rd, h3.rd, o2.rd, h1.rd, h.rd], by rw [o.wr, wr7, wr6, wr5, h.wr],
    by rw [o.sp, sp7, sp6, h5.sp, h4.sp, h3.sp, o2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [hv .v16 (by decide)]; exact h.cs.q, by rw [hv .v17 (by decide)]; exact h.cs.h⟩,
    ⟨by rw [hv .v18 (by decide)]; exact h.K.1, by rw [hv .v19 (by decide)]; exact h.K.2.1,
     by rw [hv .v20 (by decide)]; exact h.K.2.2.1, by rw [hv .v21 (by decide)]; exact h.K.2.2.2.1,
     by rw [hv .v22 (by decide)]; exact h.K.2.2.2.2⟩,
    ?_, by rw [o.mem]; exact f7⟩, by rw [show 256 / (width5.c * 4) = 8 from rfl] at uc; exact uc⟩
  rw [o.mem, show width5.c * 4 * (k + 1) = 32 * k + 16 + 16 by simp [width5]; omega_arith]
  exact o7

end VG.Proof.MlKem1024.AArch64.DD

end

end

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decode_decompress`

The contract, the dispatch on `len` to the loop of each width (`loop5_ok`, `loop11_ok`, from
`Proof/MlKem1024/AArch64/CodecV/` and the loops of ML-KEM-768's vector codecs), and constant time:
every address and branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem1024_decode_decompress(b = x0, len = x1, d =
w2, f = x3)`: if `d` is 5 or 11 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`, reduced.
The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ Proof.MlKem1024.compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_bytesVec)
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} {c : Prog isa} {s₀ s : State} (hs : decodeDecompressAArch64.pre s₀)
    (hd : ((s₀.gpr .x2).setWidth 32).toNat = w.d) (hk : Keep [.x9] s₀ s) (hm : s.mem = s₀.mem)
    (hl : ∀ s, Pre w s → WP isa c s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (fP s) (decodeDecompress w.d (B w s))) :
    WP isa c s fun s' => s'.sp = s₀.sp ∧ decodeDecompressAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, hlen⟩ := hs
  rw [hd] at hlen
  have e0 : bP s = s₀.gpr .x0 := hk.get .x0
  have e3 : fP s = s₀.gpr .x3 := hk.get .x3
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, bR, e0, hlen], by rw [hk.wr, h2, e3], by rw [e3, bR, e0, ← hlen]; exact h3⟩
  refine WP.mono (hl s hp) fun s' ⟨_, _, sp, e⟩ => ⟨by rw [sp, hk.sp], ?_⟩
  show PolyIs s'.mem (s₀.gpr .x3) (decodeDecompress ((s₀.gpr .x2).setWidth 32).toNat
    (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
  rw [hlen, hd, ← e3, ← e0, ← hm]
  exact e

theorem loop5_ok {s₀ : State} (hp : Pre width5 s₀) :
    WP isa (ddLoop 5 8 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++
      bytesVec .v21 dd10IdxHi ++ dupW .v22 31) dd5Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.sp = s₀.sp ∧ PolyIs s'.mem (fP s₀) (decodeDecompress width5.d (B width5 s₀)) :=
  dloop_ok width5_ok (Ng := 4) (K := K5) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (dupW .v22 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 => wp_dupW (by decide) fun s5 g5 v5 l5 =>
          wp_nil ⟨(((g1.trans g2).trans g3).trans g4).trans g5,
            fun r a b c d e _ => by rw [v5 r e, v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v5 .v18 (by decide), v4 .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide)]; exact l1,
            by rw [v5 .v19 (by decide), v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            by rw [v5 .v20 (by decide), v4 .v20 (by decide), e3, dd10idx],
            by rw [v5 .v21 (by decide), e4, dd10idxHi], l5⟩)
    (fun _ _ hv hk => by rw [K5, hv]; exact hk)
    fun _ hk _ h => step5 hp hk h

theorem dd11idx : ∀ g < 4, setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + ((dd11Idx g).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + ((dd11Idx g).getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + ((dd11Idx g).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec (dd11Idx g) := by decide +kernel

theorem loop11_ok {s₀ : State} (hp : Pre width11 s₀) :
    WP isa (ddLoop 11 8 (dupW .v18 (2 ^ 22 - 1) ++ dupW .v19 2047 ++ bytesVec .v20 (dd11Idx 0) ++
      bytesVec .v21 (dd11Idx 1) ++ bytesVec .v22 (dd11Idx 2) ++ bytesVec .v23 (dd11Idx 3)) dd11Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width11.d (B width11 s₀)) :=
  dloop_ok width11_ok (Ng := 4) (K := K11) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (bytesVec .v23 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 =>
        wp_bytesVec fun s5 g5 v5 e5 => wp_bytesVec fun s6 g6 v6 e6 =>
          wp_nil ⟨((((g1.trans g2).trans g3).trans g4).trans g5).trans g6,
            fun r a b c d e f => by rw [v6 r f, v5 r e, v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v6 .v18 (by decide), v5 .v18 (by decide), v4 .v18 (by decide), v3 .v18 (by decide),
              v2 .v18 (by decide)]; exact l1,
            by rw [v6 .v19 (by decide), v5 .v19 (by decide), v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            fun g hg => by
              rcases (show g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 by omega_using [hg]) with rfl | rfl | rfl | rfl
              · show s6.v .v20 = _
                rw [v6 .v20 (by decide), v5 .v20 (by decide), v4 .v20 (by decide), e3, dd11idx 0 (by decide)]
              · show s6.v .v21 = _
                rw [v6 .v21 (by decide), v5 .v21 (by decide), e4, dd11idx 1 (by decide)]
              · show s6.v .v22 = _
                rw [v6 .v22 (by decide), e5, dd11idx 2 (by decide)]
              · show s6.v .v23 = _
                rw [e6, dd11idx 3 (by decide)]⟩)
    (fun _ _ hv hk => by rw [K11, hv]; exact hk)
    fun _ hk _ h => step11 hp hk h

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa Impl.MlKem1024.AArch64.decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  have hd' := mem_compressWidths1024 hd
  suffices h : WP isa Impl.MlKem1024.AArch64.decodeDecompress s fun s' =>
      s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 160)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases hd' with h | h <;> rw [h] at hlen <;> omega_using []
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 5 := by simp at hb; omega_using [hlen, hb]
    exact width_ok (w := width5) hs e k₂ m₂ fun _ hp => loop5_ok hp
  · have e : ((s.gpr .x2).setWidth 32).toNat = 11 := by
      simp at hb
      rcases hd' with h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width11) hs e k₂ m₂ fun _ hp => loop11_ok hp

end VG.Proof.MlKem1024.AArch64.DD
