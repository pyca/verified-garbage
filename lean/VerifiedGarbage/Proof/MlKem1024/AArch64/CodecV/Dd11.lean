module

import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dword88
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd4
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

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
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem dd11IdxReg_eq {g : Nat} (hg : g < 4) :
    dd11IdxReg g = .v20 ∨ dd11IdxReg g = .v21 ∨ dd11IdxReg g = .v22 ∨ dd11IdxReg g = .v23 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- The values of 11 bits of a group `H` of 88 bits, split as `dd11Group` splits it. -/
theorem dig11_eq (H : Nat) {m : Nat} (hm : m < 8) :
    dig 11 (fun l => if l = 0 then H % 2 ^ 64 else H / 2 ^ 44) m = H / 2 ^ (11 * m) % 2 ^ 11 := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dig, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
      Nat.reducePow, Nat.one_ne_zero, ↓reduceIte, Nat.div_one] <;> omega

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
  have hBl : ∀ j < 11, B j < 2 ^ 8 := fun j hj => by rw [← hB j hj]; exact (tableByte s.v .v4 _).isLt
  have r7 : ∀ j < 16, (vbyte (s1.v .v7) j).toNat = if j < 11 then B j else 0 := fun j hj => by
    rw [h1.v]
    have hk : (vbyte (s.v (dd11IdxReg g)) j).toNat = if j < 11 then 11 * g + j else 255 := by
      rw [hidx, toNat_idxVec _ (by
        intro x hx; simp only [dd11Idx, List.mem_map, List.mem_range] at hx; omega) hj, dd11Idx_eq g hj]
    by_cases h : j < 11
    · rw [ite_eq_left h] at hk ⊢
      rw [vbyte_tblN hj hk (by omega), hB j h]
    · rw [ite_eq_right h] at hk ⊢
      rw [vbyte_tblN_out hj hk (by omega)]; rfl
  -- the group as its low eight bytes `L` and its high three `Hh`
  have b0 := hBl 0 (by decide); have b1 := hBl 1 (by decide); have b2 := hBl 2 (by decide)
  have b3 := hBl 3 (by decide); have b4 := hBl 4 (by decide); have b5 := hBl 5 (by decide)
  have b6 := hBl 6 (by decide); have b7 := hBl 7 (by decide); have b8 := hBl 8 (by decide)
  have b9 := hBl 9 (by decide); have b10 := hBl 10 (by decide)
  generalize hL : B 0 + B 1 * 2 ^ 8 + B 2 * 2 ^ 16 + B 3 * 2 ^ 24 + B 4 * 2 ^ 32 + B 5 * 2 ^ 40 + B 6 * 2 ^ 48 +
    B 7 * 2 ^ 56 = L
  generalize hH : B 8 + B 9 * 2 ^ 8 + B 10 * 2 ^ 16 = Hh
  have Llt : L < 2 ^ 64 := by omega
  have Hlt : Hh < 2 ^ 24 := by omega
  have split : num11 B = L + 2 ^ 64 * Hh := by simp only [num11]; omega
  have nlo : num11 B % 2 ^ 64 = L := by
    rw [split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Llt]
  have nhi : num11 B / 2 ^ 64 = Hh := by
    rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt Llt, Nat.zero_add]
  have lo : (vdword (s1.v .v7) 0).toNat = num11 B % 2 ^ 64 := by
    have := dword_of_bytes (s1.v .v7) 0
    simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [this, r7 0 (by decide), r7 1 (by decide), r7 2 (by decide), r7 3 (by decide), r7 4 (by decide),
      r7 5 (by decide), r7 6 (by decide), r7 7 (by decide), nlo, ← hL]
    simp only [show (0 : Nat) < 11 by decide, show (1 : Nat) < 11 by decide, show (2 : Nat) < 11 by decide,
      show (3 : Nat) < 11 by decide, show (4 : Nat) < 11 by decide, show (5 : Nat) < 11 by decide,
      show (6 : Nat) < 11 by decide, show (7 : Nat) < 11 by decide, ite_true]
  have hi : (vdword (s1.v .v7) 1).toNat = num11 B / 2 ^ 64 := by
    have := dword_of_bytes (s1.v .v7) 1
    simp only [Nat.mul_one] at this
    rw [this, r7 8 (by decide), r7 9 (by decide), r7 10 (by decide), r7 11 (by decide), r7 12 (by decide),
      r7 13 (by decide), r7 14 (by decide), r7 15 (by decide), nhi, ← hH]
    simp only [show (8 : Nat) < 11 by decide, show (9 : Nat) < 11 by decide, show (10 : Nat) < 11 by decide,
      show ¬ (11 : Nat) < 11 by decide, show ¬ (12 : Nat) < 11 by decide, show ¬ (13 : Nat) < 11 by decide,
      show ¬ (14 : Nat) < 11 by decide, show ¬ (15 : Nat) < 11 by decide, ite_true, ite_false]
    omega
  -- the high 44 bits in the low doubleword of `v1`
  have v7a : s2.v .v7 = s1.v .v7 := h2.get .v7 (by decide)
  have d1 : (vdword (s2.v .v1) 0).toNat = num11 B % 2 ^ 64 / 2 ^ 44 := by
    rw [h2.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [lo]
  have d2 : (vdword (s4.v .v2) 0).toNat = num11 B / 2 ^ 64 * 2 ^ 20 % 2 ^ 64 := by
    rw [h4.v, vdword_ext8 _ (by decide), h3'.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [v7a, hi]
  have d5 : (vdword (s5.v .v1) 0).toNat = num11 B / 2 ^ 44 := by
    rw [h5.v, StraightV.vdword_or, BitVec.toNat_or, h4.get .v1 (by decide), h3'.get .v1 (by decide), d1, d2]
    rw [nlo, nhi, Nat.mod_eq_of_lt (show Hh * 2 ^ 20 < 2 ^ 64 by omega), or_shift (by omega), split,
      show (2 : Nat) ^ 64 = 2 ^ 44 * 2 ^ 20 from by rw [← Nat.pow_add], Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm]
  have D : DLanes (s6.v .v7) fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44 := fun l hl => by
    rw [h6.v, eval_zip1_d2]
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · rw [vdword_ofVDwords_0, h5.get .v7 (by decide), h4.get .v7 (by decide), h3'.get .v7 (by decide), v7a, lo]
      simp only [↓reduceIte]
    · rw [vdword_ofVDwords_1, d5]
      simp only [Nat.one_ne_zero, ↓reduceIte]
  have c6 : VChg [.v7, .v1, .v2, .v2, .v1, .v7] s s6 :=
    ((((h1.chg.trans h2.chg).trans h3'.chg).trans h4.chg).trans h5.chg).trans h6.chg
  have r18 : Lanes (s6.v .v18) fun _ => 2 ^ (2 * 11) - 1 := Lanes.chg c6 (by decide) h18
  have r19 : Lanes (s6.v .v19) fun _ => 2 ^ 11 - 1 := Lanes.chg c6 (by decide) h19
  refine ddSplit_ok (b := 11) (.inr rfl) r18 r19 D (k := fun a7 c7 L2 L3 => ?_)
  have cs7 : DConsts 11 a7 := hc.chg (c6.trans c7) (by decide) (by decide)
  -- the values of 11 bits of the group
  have dv : ∀ m < 8, dig 11 (fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44) m =
      num11 B / 2 ^ (11 * m) % 2 ^ 11 := fun m hm => dig11_eq _ hm
  have dlt : ∀ m, dig 11 (fun l => if l = 0 then num11 B % 2 ^ 64 else num11 B / 2 ^ 44) m < 2 ^ 11 :=
    fun m => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) cs7.q cs7.h (by decide) L2
    fun e _ => dlt e) fun b1 ⟨e1, r2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (cs7.chg e1).q (cs7.chg e1).h (by decide)
    (Lanes.chg e1 (by decide) L3) fun e _ => dlt _) fun b2 ⟨e2, r3⟩ => ?_
  have c := (c6.trans c7).trans (e1.trans e2)
  simp only [List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ⟨by omega, by omega⟩ ht
    (by rw [c.mem]; exact hcu) (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg e2 (by decide) r2) fun e he => by rw [hval e (by omega), dv e (by omega)])
    (vword_G r3 fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega), dv (4 + e) (by omega)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r a b d e => by rw [st.v, c.v r (by simp [a, b, d, e])]) o f

end VG.Proof.MlKem1024.AArch64.CodecV
