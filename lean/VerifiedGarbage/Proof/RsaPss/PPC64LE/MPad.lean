module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes

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
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_sub wp_xor wp_and wp_or wp_lsr wp_lsl wp_mov
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


/-- `M'` with the length field `len` ORed into the end of block `b` under
the mask of `b = fb`, for the first `n` blocks of `B` bytes. -/
def vLen (V : Nat → Byte) (len : List Byte) (B L fb : Nat) : Nat → Nat → Byte
  | 0 => V
  | n + 1 => fun o => if oY + B * n + (B - L) ≤ o ∧ o < oY + B * n + B then
      vLen V len B L fb n o ||| (if n = fb then len.getD (o - (oY + B * n + (B - L))) 0 else 0)
    else vLen V len B L fb n o

/-- Bytes from block `n` on are as in `V`. -/
theorem vLen_out (V : Nat → Byte) (len : List Byte) (B L fb : Nat) :
    ∀ n o, oY + B * n ≤ o → vLen V len B L fb n o = V o
  | 0, _, _ => rfl
  | n + 1, o, h => by
    have : B * n + B = B * (n + 1) := (Nat.mul_succ B n).symm
    simp only [vLen]
    rw [ifn (by omega), vLen_out V len B L fb n o (by have := Nat.mul_le_mul_left B (Nat.le_succ n); omega)]

/-- Byte `k` of block `b < n`. -/
theorem vLen_at (V : Nat → Byte) (len : List Byte) {B L : Nat} (fb : Nat) (hLB : L ≤ B) :
    ∀ n {b k : Nat}, b < n → k < B → vLen V len B L fb n (oY + B * b + k) =
      V (oY + B * b + k) ||| (if b = fb ∧ B - L ≤ k then len.getD (k - (B - L)) 0 else 0)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, b, k, hb, hk => by
    simp only [vLen]
    by_cases e : b = n
    · subst e
      rw [vLen_out V len B L fb b _ (by omega)]
      by_cases hk' : B - L ≤ k
      · rw [ifp ⟨by omega, by omega⟩, show oY + B * b + k - (oY + B * b + (B - L)) = k - (B - L) by omega]
        by_cases e' : b = fb
        · rw [ifp e', ifp ⟨e', hk'⟩]
        · rw [ifn e', ifn (fun h => e' h.1)]
      · rw [ifn (by omega), ifn (fun h => hk' h.2)]
        exact BitVec.or_zero.symm
    · have hb' : b < n := by omega
      have : B * (b + 1) ≤ B * n := Nat.mul_le_mul_left B hb'
      rw [ifn (by rw [Nat.mul_succ] at this; omega), vLen_at V len fb hLB n hb' hk]

/-- Code without calls that keeps the link register, if none of its
instructions writes it. -/
theorem wp_lr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) (hc : c.noCalls = true)
    (hi : (instrs c).all (fun i => !i.writesLr) = true) : WP isa c s fun s' => Q s' ∧ s'.lr = s.lr :=
  let ⟨t, s', he, hq⟩ := h
  ⟨t, s', he, hq, Exec.lr he hc hi⟩

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `lenField`: with `ℓ` in `r29`, the length field to `oLen` and the last
block's index into `r27`. -/
theorem lenField_ok {P : Params} {md : Proof.MdStream.Md P.B P.N P.L} {D' : Nat} (hs : Proof.MdStream.PPC64LE.ShapeD md D')
    (hlr : (instrs (.block P.len : Prog isa)).all (fun i => !i.writesLr) = true)
    (hX : P.N + P.B - P.L ≤ oLen) (hL16 : P.L ≤ 16) (hlg7 : lg P ≤ 7) {t : State} (h : Base Sp (vP D) s t) {ℓ : Nat}
    (h29 : t.gpr .r29 = BitVec.ofNat 64 ℓ) (hℓ : ℓ < 2 ^ 32) :
    WP isa (.block (lenField P)) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r26, .r8, .r11, .r27] t t' ∧
      t'.gpr .r27 = BitVec.ofNat 64 ((ℓ + P.L) / 2 ^ lg P) ∧
      t'.mem = WriteBytes.writeBytes t.mem (off (Sp s) oLen) (md.lenOf (BitVec.ofNat 64 ℓ)) := by
  have F := L.F
  have hO : oLen = 4608 := rfl
  have hR : oRsa = 8192 := rfl
  unfold lenField
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_nil ?_
  have a26 : t₁.gpr .r26 + BitVec.ofNat 64 (P.N + P.B - P.L) = off (Sp s) oLen := by
    rw [e₁, h.r14, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  refine (wp_lr (hs.len t₁ (by rw [a26, o₁.wr, h.wr]; exact sc_inW F (by omega))) rfl hlr).mono
    fun t₂ ⟨⟨g₂, rd₂, wr₂, sp₂, m₂⟩, lr₂⟩ => ?_
  have k₂ : Keep [.r26, .r8, .r11] t t₂ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₂ r hr.2.1 hr.2.2, o₁.gpr r (by simp [hr.1])], rd₂.trans o₁.rd, wr₂.trans o₁.wr, sp₂.trans o₁.sp,
    lr₂.trans o₁.lr⟩
  refine wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_lsr (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Keep [.r26, .r8, .r11, .r27] t t₄ := (k₂.trans (o₃.keep.trans o₄.keep)).mono
  have hm : t₄.mem = WriteBytes.writeBytes t.mem (off (Sp s) oLen) (md.lenOf (BitVec.ofNat 64 ℓ)) := by
    rw [o₄.mem, o₃.mem, m₂, a26, o₁.get .r29, h29, o₁.mem]
  refine ⟨h.wb F k₄ (by rw [md.lenOf_length]; omega) hm, k₄, ?_, hm⟩
  rw [e₄, e₃, k₂.get .r29, h29, BitVec.ofNat_add_ofNat, Proof.MdStream.PPC64LE.ofNat_shr (by omega)]

/-- `lenLoop`, with `nbm` in `r28`, the last block's index `fb` in `r27` and
the length field `len` at `oLen`. -/
theorem lenLoop_ok {P : Params} (hB : P.B = 64 ∨ P.B = 128) (hLB : P.L < P.B) (hL0 : 0 < P.L) {t : State}
    (h : Base Sp (vP D) s t) {nbm fb : Nat} (h28 : t.gpr .r28 = BitVec.ofNat 64 nbm)
    (h27 : t.gpr .r27 = BitVec.ofNat 64 fb) (hn0 : 0 < nbm) (hnb : nbm * P.B ≤ 2048) (hfb : fb < 2 ^ 63)
    {len : List Byte} (hlen : ∀ j < P.L, view t.mem (Sp s) (oLen + j) = len.getD j 0) :
    WP isa (lenLoop P) t fun t' => Base Sp (vP D) s t' ∧
      Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = vLen (view t.mem (Sp s)) len P.B P.L fb nbm o := by
  have F := L.F
  have hO : oLen = 4608 := rfl
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  have hn : nbm ≤ 32 := by rcases hB with e | e <;> rw [e] at hnb <;> omega
  let V := view t.mem (Sp s)
  refine WP.seq (wp_addi (h := by rcases hB with e | e <;> rw [e] <;> omega) fun t₁ o₁ e₁ =>
    wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r6, .r9] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (wp_countdown (cnt := .r9) (N := nbm) (by omega) hn0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t₃ u ∧
      u.gpr .r4 = off (Sp s) (oY + P.B * i + (P.B - P.L)) ∧ u.gpr .r6 = BitVec.ofNat 64 i ∧
      ∀ o < oRsa, view u.mem (Sp s) o = vLen V len P.B P.L fb i o) ?_
    ⟨h.only F k₃, Keep.refl _ _, by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; show _ = Sp s + _; congr 2; omega,
      by rw [o₃.get .r6, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃, o₂.get .r28, o₁.get .r28, h28]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₃.keep.trans ku).mono, vu⟩
  intro i hi u ⟨bu, ku, u4, u6, vu⟩ _
  have hBi : P.B * (i + 1) ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left _ hi) (by rw [Nat.mul_comm]; exact hnb)
  have hBi' : P.B * i + P.B ≤ 2048 := by rw [← Nat.mul_succ]; exact hBi
  -- The mask of `i = fb`, `oLen` and `L`.
  refine WP.seq (wp_xor fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide)
    fun u₄ p₄ f₄ => wp_sub fun u₅ p₅ f₅ => wp_addi (h := by decide) fun u₆ p₆ f₆ =>
    wp_li (by rcases hB with e | e <;> omega) fun u₇ p₇ f₇ => wp_nil ?_)
  have k₇ : Only [.r7, .r12, .r5, .r10] u u₇ :=
    (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
  have g7 : u₇.gpr .r7 = if i = fb then BitVec.allOnes 64 else 0#64 := by
    rw [p₇.get .r7, p₆.get .r7, f₅, f₄, p₄.get .r7, f₃, f₂, f₁, u6, ku.get .r27, k₃.get .r27, h27,
      eq_mask (by omega) hfb]
  have bu₇ := bu.only F k₇
  -- The field's bytes.
  have hBn : P.B * i ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left P.B (Nat.le_of_lt hi)) (by rw [Nat.mul_comm]; exact hnb)
  let W := vLen V len P.B P.L fb i
  have g5 : u₇.gpr .r5 = off (Sp s) (oLen + 0) := by
    rw [p₇.get .r5, f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14, bu.r14]; rfl
  let a := oY + P.B * i + (P.B - P.L)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r10) (N := P.L) (by omega) hL0
    (fun j w => Base Sp (vP D) s w ∧ Keep [.r4, .r5, .r8, .r10, .r11] u₇ w ∧ w.gpr .r4 = off (Sp s) (a + j) ∧
      w.gpr .r5 = off (Sp s) (oLen + j) ∧ ∀ o < oRsa, view w.mem (Sp s) o =
        if a ≤ o ∧ o < a + j then W o ||| (if i = fb then len.getD (o - a) 0 else 0) else W o) ?_
    ⟨bu₇, Keep.refl _ _, (by rw [k₇.get .r4, u4]; rfl), g5, fun o ho => by rw [ifn (by omega), k₇.mem, vu o ho]⟩
    (by rw [f₇]))
    fun w ⟨bw, kw, w4, _, vw⟩ => ?_)
  · intro j hj w ⟨bw, kw, w4, w5, vw⟩ _
    refine wp_lbz (a := off (Sp s) (oLen + j)) (by rw [w5, BitVec.add_zero])
      (by rw [bw.wr]; exact sc_inR F (by omega) _) fun w₁ q₁ g₁ => ?_
    refine wp_and fun w₂ q₂ g₂ => ?_
    refine wp_lbz (a := off (Sp s) (a + j)) (by rw [q₂.get .r4, q₁.get .r4, w4, BitVec.add_zero])
      (by rw [q₂.rd, q₂.wr, q₁.rd, q₁.wr, bw.wr]; exact sc_inR F (by omega) _) fun w₃ q₃ g₃ => ?_
    refine wp_or fun w₄ q₄ g₄ => ?_
    have k₄ : Only [.r8, .r11] w w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
    refine wp_stb (a := off (Sp s) (a + j)) (by rw [k₄.get .r4, w4, BitVec.add_zero])
      (by rw [k₄.wr, bw.wr]; exact sc_inW F (by omega)) fun w₅ m₅ => ?_
    refine wp_addi fun w₆ q₆ g₆ => wp_addi fun w₇ q₇ g₇ => wp_subi fun w₈ q₈ g₈ => wp_nil ?_
    have vl : w.mem (off (Sp s) (oLen + j)) = len.getD j 0 := by
      have e1 := vw (oLen + j) (by omega)
      rw [ifn (by omega)] at e1
      have e2 : W (oLen + j) = V (oLen + j) := vLen_out _ _ _ _ _ _ _ (by omega)
      have e3 := vu (oLen + j) (by omega)
      exact e1.trans (e2.trans (hlen j hj))
    have vy : w.mem (off (Sp s) (a + j)) = W (a + j) := by
      have := vw (a + j) (by omega); rw [ifn (by omega)] at this; exact this
    have hb : (w₄.gpr .r11).setWidth 8 = W (a + j) ||| (if i = fb then len.getD j 0 else 0) := by
      rw [g₄, g₃, q₃.get .r8, g₂, g₁, q₁.get .r7, kw.get .r7, g7, q₂.mem, q₁.mem, vl, vy]
      have := orMask (W (a + j)) (len.getD j 0) (decide (i = fb))
      simp only [decide_eq_true_eq] at this
      exact this
    have q : Keep [.r8, .r11, .r4, .r5, .r10] w w₈ :=
      (k₄.keep.trans (m₅.keep.trans (q₆.keep.trans (q₇.keep.trans q₈.keep)))).mono
    have hm : w₈.mem = w.mem.writeW (off (Sp s) (a + j)) (W (a + j) ||| (if i = fb then len.getD j 0 else 0)) := by
      rw [q₈.mem, q₇.mem, q₆.mem, m₅.mem, hb, k₄.mem]
    refine ⟨⟨bw.keep F q (R := [⟨off (Sp s) (a + j), 1⟩]) (by
        rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
      (kw.trans q).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
    · rw [q₈.get .r4, q₇.get .r4, g₆, m₅.gpr, k₄.get .r4, w4]; exact off_off _ _ _
    · rw [q₈.get .r5, g₇, q₆.get .r5, m₅.gpr, k₄.get .r5, w5]; exact off_off _ _ _
    · rw [hm, view_w8 _ _ (by omega) ho, vw o ho]
      by_cases e : o = a + j
      · subst e
        rw [ifp rfl, ifp (show a ≤ a + j ∧ a + j < a + (j + 1) by omega), Nat.add_sub_cancel_left]
      · rw [ifn e]
        by_cases e' : a ≤ o ∧ o < a + j
        · rw [ifp e', ifp (show a ≤ o ∧ o < a + (j + 1) from ⟨e'.1, by omega⟩)]
        · rw [ifn e', ifn (show ¬(a ≤ o ∧ o < a + (j + 1)) by omega)]
    · rw [g₈, q₇.get .r10, q₆.get .r10, m₅.gpr, k₄.get .r10]
  -- The next block.
  refine wp_addi (h := by rcases hB with e | e <;> omega) fun w₁ q₁ g₁ => wp_addi fun w₂ q₂ g₂ =>
    wp_subi fun w₃ q₃ g₃ => wp_nil ?_
  have k₃' : Only [.r4, .r6, .r9] w w₃ := (q₁.trans (q₂.trans q₃)).mono
  refine ⟨⟨bw.only F k₃', (ku.trans ((k₇.keep.trans kw).trans k₃'.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [q₃.get .r4, q₂.get .r4, g₁, w4]
    show Sp s + _ + _ = Sp s + _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2
    rw [Nat.mul_succ]; omega
  · rw [q₃.get .r6, g₂, q₁.get .r6, kw.get .r6, k₇.get .r6, u6, BitVec.ofNat_add_ofNat]
  · rw [k₃'.mem, vw o ho]
    simp only [vLen, W, a, show oY + P.B * i + (P.B - P.L) + P.L = oY + P.B * i + P.B by omega]
  · rw [g₃, q₂.get .r9, q₁.get .r9, kw.get .r9, k₇.get .r9]

end

end VG.Proof.RsaPss.PPC64LE
