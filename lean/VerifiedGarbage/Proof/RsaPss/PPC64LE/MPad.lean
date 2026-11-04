module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: padding `M'` of a secret length

Untrusted: everything here is checked by Lean. The steps of `ctHash` before
the compression: `pad80_ok`, `0x80` ORed into byte `ℓ` of `M'` (`r29`) by a
mask over its `nbm B` bytes (`v80`); `lenField_ok`, the length field of `ℓ`
written at `oLen` by the hash function's code for it, and the last block's
index into `r27`; `lenLoop_ok`, the length field ORed into the end of that
block by a mask over every block (`vLen`). As views of our part of the
working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 view_wb sc_in sc_inR sc_inW fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_sub wp_xor wp_and wp_or wp_lsr wp_lsl
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- `M'` with `0x80` ORed into byte `ℓ`, over its first `n` bytes. -/
def v80 (V : Nat → Byte) (ℓ n : Nat) (o : Nat) : Byte :=
  if oY ≤ o ∧ o < oY + n then V o ||| (if o - oY = ℓ then 0x80 else 0) else V o

theorem or80 (b : Byte) (bit : Bool) :
    (b.setWidth 64 ||| ((if bit then BitVec.allOnes 64 else 0#64) &&& BitVec.ofNat 64 0x80)).setWidth 8 =
      b ||| (if bit then 0x80 else 0) := by
  rw [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  cases bit
  · rfl
  · rfl

theorem orMask (a b : Byte) (bit : Bool) :
    (a.setWidth 64 ||| (b.setWidth 64 &&& (if bit then BitVec.allOnes 64 else 0#64))).setWidth 8 =
      a ||| (if bit then b else 0) := by
  rw [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.setWidth_and,
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  cases bit
  · simp
  · simp only [ite_true]
    rw [show (BitVec.setWidth 8 (BitVec.allOnes 64) : Byte) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `pad80`, with `nbm` in `r28` and `ℓ` in `r29`. -/
theorem pad80_ok {P : Params} (hlg : 2 ^ lg P = P.B) (hlg7 : lg P ≤ 7) {t : State} (h : Base Sp (vP D) s t)
    {nbm ℓ : Nat} (h28 : t.gpr .r28 = BitVec.ofNat 64 nbm) (h29 : t.gpr .r29 = BitVec.ofNat 64 ℓ)
    (hnb : nbm * P.B ≤ 2048) (h0 : 0 < nbm * P.B) (hℓ : ℓ < 2 ^ 63) :
    WP isa (pad80 P) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r4, .r5, .r6, .r7, .r8, .r12] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = v80 (view t.mem (Sp s)) ℓ (nbm * P.B) o := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  let V := view t.mem (Sp s)
  have hB1 : 1 ≤ P.B := hlg ▸ Nat.one_le_two_pow
  have hn : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB1) hnb
  refine WP.seq (wp_addi (h := by decide) fun t₁ o₁ e₁ => wp_lsl (h := by omega) fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have e5 : t₃.gpr .r5 = BitVec.ofNat 64 (nbm * P.B) := by
    rw [o₃.get .r5, e₂, o₁.get .r28, h28, ← hlg, BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
    rw [Nat.mod_eq_of_lt (show nbm < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 ^ lg P < 2 ^ 64 from Nat.pow_lt_pow_right (by decide) (by omega))]
  refine WP.mono (wp_countdown (cnt := .r5) (N := nbm * P.B) (by omega) h0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8, .r12] t₃ u ∧ u.gpr .r4 = off (Sp s) (oY + i) ∧
      u.gpr .r6 = BitVec.ofNat 64 i ∧ ∀ o < oRsa, view u.mem (Sp s) o = v80 V ℓ i o) ?_
    ⟨h.only F k₃, Keep.refl _ _, by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; rfl, by rw [e₃],
      fun o _ => by rw [k₃.mem]; simp only [v80]; rw [ifn (by omega)]⟩ e5)
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₃.keep.trans ku).mono, vu⟩
  intro i hi u ⟨bu, ku, u4, u6, vu⟩ _
  refine wp_xor fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide)
    fun u₄ p₄ f₄ => wp_sub fun u₅ p₅ f₅ => wp_li (by decide) fun u₆ p₆ f₆ => wp_and fun u₇ p₇ f₇ => ?_
  have k₇ : Only [.r7, .r12, .r8] u u₇ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
  have g7 : u₇.gpr .r7 = (if i = ℓ then BitVec.allOnes 64 else 0#64) &&& BitVec.ofNat 64 0x80 := by
    rw [f₇, p₆.get .r7, f₅, f₄, p₄.get .r7, f₃, f₂, f₁, u6, ku.get .r29, k₃.get .r29, h29, f₆,
      eq_mask (by omega) hℓ]
  refine wp_lbz (a := off (Sp s) (oY + i)) (by rw [k₇.get .r4, u4, BitVec.add_zero])
    (by rw [k₇.rd, k₇.wr, bu.wr]; exact sc_inR F (by omega) _) fun u₈ p₈ f₈ => ?_
  refine wp_or fun u₉ p₉ f₉ => ?_
  have k₉ : Only [.r7, .r12, .r8] u u₉ := (k₇.trans (p₈.trans p₉)).mono
  refine wp_stb (a := off (Sp s) (oY + i)) (by rw [k₉.get .r4, u4, BitVec.add_zero])
    (by rw [k₉.wr, bu.wr]; exact sc_inW F (by omega)) fun u₁₀ m₁₀ => ?_
  refine wp_addi fun u₁₁ p₁₁ f₁₁ => wp_addi fun u₁₂ p₁₂ f₁₂ => wp_subi fun u₁₃ p₁₃ f₁₃ => wp_nil ?_
  have vi : u.mem (off (Sp s) (oY + i)) = V (oY + i) := by
    have := vu (oY + i) (by omega); simp only [v80] at this; rw [ifn (by omega)] at this; exact this
  have hb : (u₉.gpr .r8).setWidth 8 = V (oY + i) ||| (if i = ℓ then 0x80 else 0) := by
    rw [f₉, f₈, p₈.get .r7, g7, k₇.mem, vi]
    have := or80 (V (oY + i)) (decide (i = ℓ))
    simp only [decide_eq_true_eq] at this
    exact this
  have q : Keep [.r7, .r12, .r8, .r4, .r6, .r5] u u₁₃ :=
    (k₉.keep.trans (m₁₀.keep.trans (p₁₁.keep.trans (p₁₂.keep.trans p₁₃.keep)))).mono
  have hm : u₁₃.mem = u.mem.writeW (off (Sp s) (oY + i)) (V (oY + i) ||| (if i = ℓ then 0x80 else 0)) := by
    rw [p₁₃.mem, p₁₂.mem, p₁₁.mem, m₁₀.mem, hb, k₉.mem]
  refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (oY + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    (ku.trans q).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₁₃.get .r4, p₁₂.get .r4, f₁₁, m₁₀.gpr, k₉.get .r4, u4]; exact off_off _ _ _
  · rw [p₁₃.get .r6, f₁₂, p₁₁.get .r6, m₁₀.gpr, k₉.get .r6, u6, BitVec.ofNat_add_ofNat]
  · rw [hm, view_w8 _ _ (by omega) ho, vu o ho]
    simp only [v80]
    by_cases e : o = oY + i
    · subst e
      rw [ifp rfl, ifp (show oY ≤ oY + i ∧ oY + i < oY + (i + 1) by omega), Nat.add_sub_cancel_left]
    · rw [ifn e]
      by_cases e' : oY ≤ o ∧ o < oY + i
      · rw [ifp e', ifp (show oY ≤ o ∧ o < oY + (i + 1) from ⟨e'.1, by omega⟩)]
      · rw [ifn e', ifn (show ¬(oY ≤ o ∧ o < oY + (i + 1)) by omega)]
  · rw [f₁₃, p₁₂.get .r5, p₁₁.get .r5, m₁₀.gpr, k₉.get .r5]

end

end VG.Proof.RsaPss.PPC64LE
