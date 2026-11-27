module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MComp
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `RsaPss.PPC64LE.MPad`, which this module and modules that import it used -/

section

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
  obtain hB1 : 1 ≤ P.B := hlg ▸ Nat.one_le_two_pow
  obtain hn : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB1) hnb
  refine WP.seq (wp_addi (h := by decide) fun t₁ o₁ e₁ => wp_lsl (h := by omega_using [hlg7]) fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  obtain k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain e5 : t₃.gpr .r5 = BitVec.ofNat 64 (nbm * P.B) := by
    rw [o₃.get .r5, e₂, o₁.get .r28, h28, ← hlg, BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
    rw [Nat.mod_eq_of_lt (show nbm < 2 ^ 64 by omega_using [hn]),
      Nat.mod_eq_of_lt (show 2 ^ lg P < 2 ^ 64 from Nat.pow_lt_pow_right (by decide) (by omega_using [hlg7]))]
  refine WP.mono (wp_countdown (cnt := .r5) (N := nbm * P.B) (by omega_using [hnb]) h0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8, .r12] t₃ u ∧ u.gpr .r4 = off (Sp s) (oY + i) ∧
      u.gpr .r6 = BitVec.ofNat 64 i ∧ ∀ o < oRsa, view u.mem (Sp s) o = v80 V ℓ i o) ?_
    ⟨h.only F k₃, Keep.refl _ _, by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; rfl, by rw [e₃],
      fun o _ => by rw [k₃.mem]; simp only [v80]; rw [ifn (by omega_using [])]⟩ e5)
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₃.keep.trans ku).mono, vu⟩
  intro i hi u ⟨bu, ku, u4, u6, vu⟩ _
  refine wp_xor fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide)
    fun u₄ p₄ f₄ => wp_sub fun u₅ p₅ f₅ => wp_li (by decide) fun u₆ p₆ f₆ => wp_and fun u₇ p₇ f₇ => ?_
  obtain k₇ : Only [.r7, .r12, .r8] u u₇ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
  obtain g7 : u₇.gpr .r7 = (if i = ℓ then BitVec.allOnes 64 else 0#64) &&& BitVec.ofNat 64 0x80 := by
    rw [f₇, p₆.get .r7, f₅, f₄, p₄.get .r7, f₃, f₂, f₁, u6, ku.get .r29, k₃.get .r29, h29, f₆,
      eq_mask (by omega_using [hnb, hi]) hℓ]
  refine wp_lbz (a := off (Sp s) (oY + i)) (by rw [k₇.get .r4, u4, BitVec.add_zero])
    (by rw [k₇.rd, k₇.wr, bu.wr]; exact sc_inR F (by omega_using [hnb, hR, hY, hi]) _) fun u₈ p₈ f₈ => ?_
  refine wp_or fun u₉ p₉ f₉ => ?_
  obtain k₉ : Only [.r7, .r12, .r8] u u₉ := (k₇.trans (p₈.trans p₉)).mono
  refine wp_stb (a := off (Sp s) (oY + i)) (by rw [k₉.get .r4, u4, BitVec.add_zero])
    (by rw [k₉.wr, bu.wr]; exact sc_inW F (by omega_using [hnb, hR, hY, hi])) fun u₁₀ m₁₀ => ?_
  refine wp_addi fun u₁₁ p₁₁ f₁₁ => wp_addi fun u₁₂ p₁₂ f₁₂ => wp_subi fun u₁₃ p₁₃ f₁₃ => wp_nil ?_
  obtain vi : u.mem (off (Sp s) (oY + i)) = V (oY + i) := by
    have := vu (oY + i) (by omega_using [hnb, hR, hY, hi]); simp only [v80] at this; rw [ifn (by omega_using [])] at this; exact this
  obtain hb : (u₉.gpr .r8).setWidth 8 = V (oY + i) ||| (if i = ℓ then 0x80 else 0) := by
    rw [f₉, f₈, p₈.get .r7, g7, k₇.mem, vi]
    have := or80 (V (oY + i)) (decide (i = ℓ))
    simp only [decide_eq_true_eq] at this
    exact this
  obtain q : Keep [.r7, .r12, .r8, .r4, .r6, .r5] u u₁₃ :=
    (k₉.keep.trans (m₁₀.keep.trans (p₁₁.keep.trans (p₁₂.keep.trans p₁₃.keep)))).mono
  obtain hm : u₁₃.mem = u.mem.writeW (off (Sp s) (oY + i)) (V (oY + i) ||| (if i = ℓ then 0x80 else 0)) := by
    rw [p₁₃.mem, p₁₂.mem, p₁₁.mem, m₁₀.mem, hb, k₉.mem]
  refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (oY + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega_using [hnb, hR, hY, hi]))),
    (ku.trans q).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₁₃.get .r4, p₁₂.get .r4, f₁₁, m₁₀.gpr, k₉.get .r4, u4]; exact off_off _ _ _
  · rw [p₁₃.get .r6, f₁₂, p₁₁.get .r6, m₁₀.gpr, k₉.get .r6, u6, BitVec.ofNat_add_ofNat]
  · rw [hm, view_w8 _ _ (by omega_using [hnb, hR, hY, hi]) ho, vu o ho]
    simp only [v80]
    by_cases e : o = oY + i
    · subst e
      rw [ifp rfl, ifp (show oY ≤ oY + i ∧ oY + i < oY + (i + 1) by omega_using []), Nat.add_sub_cancel_left]
    · rw [ifn e]
      by_cases e' : oY ≤ o ∧ o < oY + i
      · rw [ifp e', ifp (show oY ≤ o ∧ o < oY + (i + 1) from ⟨e'.1, by omega_using [e']⟩)]
      · rw [ifn e', ifn (show ¬(oY ≤ o ∧ o < oY + (i + 1)) by omega_using [e, e'])]
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
    rw [ifn (by omega_using [h, this]), vLen_out V len B L fb n o (by have := Nat.mul_le_mul_left B (Nat.le_succ n); omega_arith)]

/-- Byte `k` of block `b < n`. -/
theorem vLen_at (V : Nat → Byte) (len : List Byte) {B L : Nat} (fb : Nat) (hLB : L ≤ B) :
    ∀ n {b k : Nat}, b < n → k < B → vLen V len B L fb n (oY + B * b + k) =
      V (oY + B * b + k) ||| (if b = fb ∧ B - L ≤ k then len.getD (k - (B - L)) 0 else 0)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, b, k, hb, hk => by
    simp only [vLen]
    by_cases e : b = n
    · subst e
      rw [vLen_out V len B L fb b _ (by omega_using [])]
      by_cases hk' : B - L ≤ k
      · rw [ifp ⟨by omega_using [hk'], by omega_using [hk]⟩, show oY + B * b + k - (oY + B * b + (B - L)) = k - (B - L) by omega_using []]
        by_cases e' : b = fb
        · rw [ifp e', ifp ⟨e', hk'⟩]
        · rw [ifn e', ifn (fun h => e' h.1)]
      · rw [ifn (by omega_using [hk']), ifn (fun h => hk' h.2)]
        exact BitVec.or_zero.symm
    · have hb' : b < n := by omega_using [hb, e]
      have : B * (b + 1) ≤ B * n := Nat.mul_le_mul_left B hb'
      rw [ifn (by rw [Nat.mul_succ] at this; omega_using [hk, this]), vLen_at V len fb hLB n hb' hk]

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
  refine wp_addi (h := by omega_using [hO]) fun t₁ o₁ e₁ => wp_nil ?_
  obtain a26 : t₁.gpr .r26 + BitVec.ofNat 64 (P.N + P.B - P.L) = off (Sp s) oLen := by
    rw [e₁, h.r14, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using [hX]
  refine (wp_lr (hs.len t₁ (by rw [a26, o₁.wr, h.wr]; exact sc_inW F (by omega_using [hL16, hO, hR]))) rfl hlr).mono
    fun t₂ ⟨⟨g₂, rd₂, wr₂, sp₂, m₂⟩, lr₂⟩ => ?_
  obtain k₂ : Keep [.r26, .r8, .r11] t t₂ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₂ r hr.2.1 hr.2.2, o₁.gpr r (by simp [hr.1])], rd₂.trans o₁.rd, wr₂.trans o₁.wr, sp₂.trans o₁.sp,
    lr₂.trans o₁.lr⟩
  refine wp_addi (h := by omega_using [hL16]) fun t₃ o₃ e₃ => wp_lsr (h := by omega_using [hlg7]) fun t₄ o₄ e₄ => wp_nil ?_
  obtain k₄ : Keep [.r26, .r8, .r11, .r27] t t₄ := (k₂.trans (o₃.keep.trans o₄.keep)).mono
  obtain hm : t₄.mem = WriteBytes.writeBytes t.mem (off (Sp s) oLen) (md.lenOf (BitVec.ofNat 64 ℓ)) := by
    rw [o₄.mem, o₃.mem, m₂, a26, o₁.get .r29, h29, o₁.mem]
  refine ⟨h.wb F k₄ (by rw [md.lenOf_length]; omega_using [hL16, hO, hR]) hm, k₄, ?_, hm⟩
  rw [e₄, e₃, k₂.get .r29, h29, BitVec.ofNat_add_ofNat, Proof.MdStream.PPC64LE.ofNat_shr (by omega_arith)]

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
  obtain hn : nbm ≤ 32 := by rcases hB with e | e <;> rw [e] at hnb <;> omega_using [hnb]
  let V := view t.mem (Sp s)
  refine WP.seq (wp_addi (h := by rcases hB with e | e <;> rw [e] <;> omega_using [hY]) fun t₁ o₁ e₁ =>
    wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  obtain k₃ : Only [.r4, .r6, .r9] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (wp_countdown (cnt := .r9) (N := nbm) (by omega_using [hn]) hn0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t₃ u ∧
      u.gpr .r4 = off (Sp s) (oY + P.B * i + (P.B - P.L)) ∧ u.gpr .r6 = BitVec.ofNat 64 i ∧
      ∀ o < oRsa, view u.mem (Sp s) o = vLen V len P.B P.L fb i o) ?_
    ⟨h.only F k₃, Keep.refl _ _, by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; show _ = Sp s + _; congr 2; omega_using [hLB],
      by rw [o₃.get .r6, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃, o₂.get .r28, o₁.get .r28, h28]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₃.keep.trans ku).mono, vu⟩
  intro i hi u ⟨bu, ku, u4, u6, vu⟩ _
  obtain hBi : P.B * (i + 1) ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left _ hi) (by rw [Nat.mul_comm]; exact hnb)
  obtain hBi' : P.B * i + P.B ≤ 2048 := by rw [← Nat.mul_succ]; exact hBi
  -- The mask of `i = fb`, `oLen` and `L`.
  refine WP.seq (wp_xor fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide)
    fun u₄ p₄ f₄ => wp_sub fun u₅ p₅ f₅ => wp_addi (h := by decide) fun u₆ p₆ f₆ =>
    wp_li (by rcases hB with e | e <;> omega_using [hLB, hBi']) fun u₇ p₇ f₇ => wp_nil ?_)
  obtain k₇ : Only [.r7, .r12, .r5, .r10] u u₇ :=
    (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
  obtain g7 : u₇.gpr .r7 = if i = fb then BitVec.allOnes 64 else 0#64 := by
    rw [p₇.get .r7, p₆.get .r7, f₅, f₄, p₄.get .r7, f₃, f₂, f₁, u6, ku.get .r27, k₃.get .r27, h27,
      eq_mask (by omega_using [hn, hi]) hfb]
  obtain bu₇ := bu.only F k₇
  -- The field's bytes.
  obtain hBn : P.B * i ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left P.B (Nat.le_of_lt hi)) (by rw [Nat.mul_comm]; exact hnb)
  let W := vLen V len P.B P.L fb i
  obtain g5 : u₇.gpr .r5 = off (Sp s) (oLen + 0) := by
    rw [p₇.get .r5, f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14, bu.r14]; rfl
  let a := oY + P.B * i + (P.B - P.L)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r10) (N := P.L) (by omega_using [hB, hLB]) hL0
    (fun j w => Base Sp (vP D) s w ∧ Keep [.r4, .r5, .r8, .r10, .r11] u₇ w ∧ w.gpr .r4 = off (Sp s) (a + j) ∧
      w.gpr .r5 = off (Sp s) (oLen + j) ∧ ∀ o < oRsa, view w.mem (Sp s) o =
        if a ≤ o ∧ o < a + j then W o ||| (if i = fb then len.getD (o - a) 0 else 0) else W o) ?_
    ⟨bu₇, Keep.refl _ _, (by rw [k₇.get .r4, u4]; rfl), g5, fun o ho => by rw [ifn (by omega_using []), k₇.mem, vu o ho]⟩
    (by rw [f₇]))
    fun w ⟨bw, kw, w4, _, vw⟩ => ?_)
  · intro j hj w ⟨bw, kw, w4, w5, vw⟩ _
    refine wp_lbz (a := off (Sp s) (oLen + j)) (by rw [w5, BitVec.add_zero])
      (by rw [bw.wr]; exact sc_inR F (by omega_using [hB, hLB, hL0, hn0, hnb, hO, hR, hn, hi, hBi, hBi', hBn, hj]) _) fun w₁ q₁ g₁ => ?_
    refine wp_and fun w₂ q₂ g₂ => ?_
    refine wp_lbz (a := off (Sp s) (a + j)) (by rw [q₂.get .r4, q₁.get .r4, w4, BitVec.add_zero])
      (by rw [q₂.rd, q₂.wr, q₁.rd, q₁.wr, bw.wr]; exact sc_inR F (by omega) _) fun w₃ q₃ g₃ => ?_
    refine wp_or fun w₄ q₄ g₄ => ?_
    obtain k₄ : Only [.r8, .r11] w w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
    refine wp_stb (a := off (Sp s) (a + j)) (by rw [k₄.get .r4, w4, BitVec.add_zero])
      (by rw [k₄.wr, bw.wr]; exact sc_inW F (by omega)) fun w₅ m₅ => ?_
    refine wp_addi fun w₆ q₆ g₆ => wp_addi fun w₇ q₇ g₇ => wp_subi fun w₈ q₈ g₈ => wp_nil ?_
    obtain vl : w.mem (off (Sp s) (oLen + j)) = len.getD j 0 := by
      obtain e1 := vw (oLen + j) (by omega_using [hB, hLB, hL0, hn0, hnb, hO, hR, hn, hi, hBi, hBi', hBn, hj])
      rw [ifn (by omega)] at e1
      obtain e2 : W (oLen + j) = V (oLen + j) := vLen_out _ _ _ _ _ _ _ (by omega_using [hO, hY, hBi'])
      obtain e3 := vu (oLen + j) (by omega_using [hB, hLB, hL0, hn0, hnb, hO, hR, hn, hi, hBi, hBi', hBn, hj])
      exact e1.trans (e2.trans (hlen j hj))
    obtain vy : w.mem (off (Sp s) (a + j)) = W (a + j) := by
      have := vw (a + j) (by omega); rw [ifn (by omega_using [])] at this; exact this
    obtain hb : (w₄.gpr .r11).setWidth 8 = W (a + j) ||| (if i = fb then len.getD j 0 else 0) := by
      rw [g₄, g₃, q₃.get .r8, g₂, g₁, q₁.get .r7, kw.get .r7, g7, q₂.mem, q₁.mem, vl, vy]
      have := orMask (W (a + j)) (len.getD j 0) (decide (i = fb))
      simp only [decide_eq_true_eq] at this
      exact this
    obtain q : Keep [.r8, .r11, .r4, .r5, .r10] w w₈ :=
      (k₄.keep.trans (m₅.keep.trans (q₆.keep.trans (q₇.keep.trans q₈.keep)))).mono
    obtain hm : w₈.mem = w.mem.writeW (off (Sp s) (a + j)) (W (a + j) ||| (if i = fb then len.getD j 0 else 0)) := by
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
        rw [ifp rfl, ifp (show a ≤ a + j ∧ a + j < a + (j + 1) by omega_using []), Nat.add_sub_cancel_left]
      · rw [ifn e]
        by_cases e' : a ≤ o ∧ o < a + j
        · rw [ifp e', ifp (show a ≤ o ∧ o < a + (j + 1) from ⟨e'.1, by omega_using [e']⟩)]
        · rw [ifn e', ifn (show ¬(a ≤ o ∧ o < a + (j + 1)) by omega_using [e, e'])]
    · rw [g₈, q₇.get .r10, q₆.get .r10, m₅.gpr, k₄.get .r10]
  -- The next block.
  refine wp_addi (h := by rcases hB with e | e <;> omega_using [hBi']) fun w₁ q₁ g₁ => wp_addi fun w₂ q₂ g₂ =>
    wp_subi fun w₃ q₃ g₃ => wp_nil ?_
  obtain k₃' : Only [.r4, .r6, .r9] w w₃ := (q₁.trans (q₂.trans q₃)).mono
  refine ⟨⟨bw.only F k₃', (ku.trans ((k₇.keep.trans kw).trans k₃'.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [q₃.get .r4, q₂.get .r4, g₁, w4]
    show Sp s + _ + _ = Sp s + _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2
    rw [Nat.mul_succ]; omega_using [hLB]
  · rw [q₃.get .r6, g₂, q₁.get .r6, kw.get .r6, k₇.get .r6, u6, BitVec.ofNat_add_ofNat]
  · rw [k₃'.mem, vw o ho]
    simp only [vLen, W, a, show oY + P.B * i + (P.B - P.L) + P.L = oY + P.B * i + P.B by omega_using [hLB]]
  · rw [g₃, q₂.get .r9, q₁.get .r9, kw.get .r9, k₇.get .r9]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS verification on PPC64LE: `ctHash`

Untrusted: everything here is checked by Lean. What `ctHash` needs of the
hash function's Merkle–Damgård code (`CtOK`: its sizes, its length field's
code, its compression function and its digest); `compLoop_ok`: every block
of `M'` compressed into the hash value at `oSt`, the hash value after block
`fb` selected at `oSel`; and `ctHash_ok`: from `M'` of `ℓ` bytes at `oY`
followed by zeros, its digest at `oDig`, by `Proof.RsaPss.pad_getD`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa tcall)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 view_wb sc_in sc_inR sc_inW sc_cov sdis cR_dis Same)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_and wp_lsr wp_lsl
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- What `ctHash` needs of a hash function's Merkle–Damgård code: its
sizes, its length field (`P.len`), its compression function `cc` and the
digest `dc` of its hash value. -/
structure CtOK (P : Params) (md : Md P.B P.N P.L) (cc dc : Prog isa) : Prop where
  dims : Dims P
  shape : ShapeD md P.N
  lenLr : (instrs (.block P.len : Prog isa)).all (fun i => !i.writesLr) = true
  callee : CalleeOk md cc
  dig : ∀ u, (digestK md).pre u → ∃ t u', Exec isa dc u t u' ∧ abiPreserved u u' ∧ (digestK md).post u u'
  digNF : dc.noFrames = true
  reloc : md.Reloc
  lenOk : ∀ n < 2 ^ 32, md.lenOk n

theorem off_add' (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

/-- The bytes of `M'`'s place, from the view `V`. -/
def yl (V : Nat → Byte) : List Byte := (List.range 2048).map fun k => V (oY + k)

theorem yl_getD {V : Nat → Byte} {k : Nat} (hk : k < 2048) : (yl V).getD k 0 = V (oY + k) := by
  simp only [yl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

/-- What the compression loop keeps after `i` blocks, from the state `t`. -/
structure CompI (D : Nat) (s : State) {P : Params} (md : Md P.B P.N P.L) (fb : Nat) (hv : md.HV) (t : State)
    (i : Nat) (u : State) : Prop where
  base : Base Sp (vP D) s u
  sy : u.syms = s.syms
  keep : ∀ r ∈ [Reg.r24, .r27], u.gpr r = t.gpr r
  r26 : u.gpr .r26 = BitVec.ofNat 64 i
  st : md.stateAt u.mem (off (Sp s) oSt) = md.compressList hv (yl (view t.mem (Sp s))) i
  sel : fb < i → md.stateAt u.mem (off (Sp s) oSel) = md.compressList hv (yl (view t.mem (Sp s))) (fb + 1)
  mem : ∀ o < oRsa, (o < oSt ∨ oY ≤ o ∧ o < oY + 2048) → view u.mem (Sp s) o = view t.mem (Sp s) o

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash}
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j Sp s p)
  {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc)
include L T ok

/-- `compLoop`, with `nbm` in `r28` and the last block's index `fb` in
`r27`. -/
theorem compLoop_ok {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {nbm fb : Nat}
    (h28 : t.gpr .r28 = BitVec.ofNat 64 nbm) (h27 : t.gpr .r27 = BitVec.ofNat 64 fb) (hn0 : 0 < nbm)
    (hnb : nbm * P.B ≤ 2048) (hfb : fb < nbm) :
    WP isa (compLoop P f j) t fun t' => CompI D s md fb (md.stateAt t.mem (off (Sp s) oSt)) t nbm t' := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hSl : oSel = 4800 := rfl
  have hW : oW = 1352 := rfl
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hN := ok.dims.N
  have hso := ok.dims.so
  have hB := ok.dims.B
  obtain hn : nbm ≤ 32 := by rcases hB with e | e <;> rw [e] at hnb <;> omega_using [hnb]
  let V := view t.mem (Sp s)
  let hv := md.stateAt t.mem (off (Sp s) oSt)
  refine WP.seq (WP.of_syms (wp_li (by decide) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  refine wp_countdown (cnt := .r28) (N := nbm) (by omega_using [hn]) hn0 (CompI D s md fb hv t) ?_
    ⟨h.only F o₁, y₁.trans sy, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> exact o₁.get _,
      e₁, by rw [o₁.mem, Md.compressList_zero], fun h => absurd h (Nat.not_lt_zero _), fun o _ _ => by rw [o₁.mem]⟩
    (by rw [o₁.get .r28, h28])
  intro i hi u I _
  obtain hBi : P.B * i + P.B ≤ 2048 := by
    rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hi) (by rw [Nat.mul_comm]; exact hnb)
  -- The arguments.
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun u₁ p₁ f₁ => wp_lsl (h := by omega_using [hlg7]) fun u₂ p₂ f₂ =>
    wp_add fun u₃ p₃ f₃ => wp_addi (h := by decide) fun u₄ p₄ f₄ => wp_li (by decide) fun u₅ p₅ f₅ =>
    wp_addi (h := by decide) fun u₆ p₆ f₆ => wp_nil fun y₆ => ?_))
  obtain k₆ : Only [.r3, .r4, .r5, .r6] u u₆ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans p₆))))).mono
  obtain b₆ := I.base.only F k₆
  obtain g4 : u₆.gpr .r4 = off (Sp s) (oY + P.B * i) := by
    rw [p₆.get .r4, p₅.get .r4, f₄, f₃, f₂, p₁.get .r26, I.r26, p₂.get .r14, p₁.get .r14, I.base.r14,
      ofNat_shl (by rw [hlg]; omega_using [hBi]), hlg]
    show _ = Sp s + _
    rw [BitVec.add_comm (BitVec.ofNat 64 _) (Sp s), BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []
  -- The compression.
  refine WP.seq (WP.mono (compM_ok F T ok.callee hN.2 hso.2 b₆ (y₆.trans I.sy) (b := P.B * i)
      (by rw [p₆.get .r3, p₅.get .r3, p₄.get .r3, p₃.get .r3, p₂.get .r3, f₁, I.base.r14])
      g4 (by rw [p₆.get .r5, f₅]) (by rw [f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14,
        I.base.r14]) (by omega_using [hBi])) fun u₇ ⟨⟨b₇, g₇, s₇, st₇⟩, y₇⟩ => ?_)
  -- The selection.
  obtain r26₇ : u₇.gpr .r26 = BitVec.ofNat 64 i := by rw [g₇ _ (by decide), k₆.get .r26, I.r26]
  obtain r27₇ : u₇.gpr .r27 = BitVec.ofNat 64 fb := by rw [g₇ _ (by decide), k₆.get .r27, I.keep .r27 (by simp), h27]
  refine WP.seq (WP.of_syms (WP.mono (selHash_ok L hN.1 hN.2 b₇ r26₇ r27₇ (by omega_using [hn, hi]) (by omega_using [hfb, hn]))
    fun u₈ ⟨b₈, k₈, v₈⟩ y₈ => ?_))
  refine WP.of_syms (wp_addi fun u₉ p₉ f₉ => wp_subi fun u₁₀ p₁₀ f₁₀ => wp_nil fun y₁₀ => ?_)
  obtain k₁₀ : Only [.r26, .r28] u₈ u₁₀ := (p₉.trans p₁₀).mono
  have m₁₀ : u₁₀.mem = u₈.mem := k₁₀.mem
  -- The bytes of the hash value at `oSt` are kept by the selection.
  obtain vSt : ∀ k < P.N, u₁₀.mem (off (Sp s) oSt + BitVec.ofNat 64 k) = u₇.mem (off (Sp s) oSt + BitVec.ofNat 64 k) :=
    fun k hk => by
      have := v₈ (oSt + k) (by omega_using [hR, hSt, hN, hk]); rw [ifn (by omega_using [hSt, hSl, hN, hk])] at this
      rw [m₁₀, off_add']; exact this
  obtain hblk : md.blockAt u.mem (off (Sp s) (oY + P.B * i)) = md.blockOf (yl V) i := by
    simp only [Md.blockAt, Md.blockOf]
    refine md.parse_congr fun k hk => ?_
    rw [yl_getD (by omega_using [hBi, hk]), off_add', show oY + P.B * i + k = oY + (P.B * i + k) by omega_using []]
    exact I.mem _ (by omega_using [hR, hY, hBi, hk]) (.inr ⟨by omega_using [], by omega_using [hBi, hk]⟩)
  obtain hst : md.stateAt u₁₀.mem (off (Sp s) oSt) = md.compressList hv (yl V) (i + 1) := by
    rw [md.stateAt_congr vSt, st₇, k₆.mem, hblk, I.st, Md.compressList_succ]
  refine ⟨⟨b₈.only F k₁₀, y₁₀.trans (y₈.trans y₇), fun r hr => ?_, ?_, hst, fun hlt => ?_, fun o ho hr => ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [k₁₀.get .r24, k₈.get .r24, g₇ _ (by decide), k₆.get .r24, I.keep .r24 (by simp)]
    · rw [k₁₀.get .r27, k₈.get .r27, r27₇, h27]
  · rw [p₁₀.get .r26, f₉, k₈.get .r26, r26₇, BitVec.ofNat_add_ofNat]
  · by_cases e : i = fb
    · subst e
      rw [← hst]
      refine ok.reloc _ _ _ _ fun k hk => ?_
      have := v₈ (oSel + k) (by omega_using [hR, hSl, hN, hk])
      rw [ifp ⟨by omega_using [], by omega_using [hk], rfl⟩, show oSt + (oSel + k - oSel) = oSt + k by omega_using []] at this
      obtain a1 : u₁₀.mem (off (Sp s) oSel + BitVec.ofNat 64 k) = u₇.mem (off (Sp s) oSt + BitVec.ofNat 64 k) := by
        rw [m₁₀, off_add', off_add']; exact this
      exact a1.trans (vSt k hk).symm
    · have hlt' : fb < i := by omega_using [hlt, e]
      rw [← I.sel hlt']
      refine md.stateAt_congr fun k hk => ?_
      obtain e8 := v₈ (oSel + k) (by omega_using [hR, hSl, hN, hk])
      rw [ifn (fun h => e h.2.2)] at e8
      obtain e7 := s₇ (oSel + k) (by omega_using [hR, hSl, hN, hk]) (by simp; omega_using [hSt, hSl, hW, hN, hso])
      rw [m₁₀, off_add']; exact e8.trans (e7.trans (by rw [k₆.mem]; rfl))
  · have e8 := v₈ o ho
    rw [ifn (by omega_using [hn0, hnb, hfb, hR, hY, hSt, hSl, hN, hB, hn, hi, hBi, ho, hr])] at e8
    obtain e7 := s₇ o ho (by simp; omega_using [hY, hSt, hW, hN, hso, hr])
    rw [m₁₀]; exact e8.trans (e7.trans (by rw [k₆.mem]; exact I.mem o ho hr))
  · rw [f₁₀, p₉.get .r28, k₈.get .r28, g₇ _ (by decide), k₆.get .r28]

end


open VG.Proof.RsaPss (lastBlk padded)

theorem or0 (x : Byte) : x ||| 0 = x := BitVec.or_zero
theorem zor (x : Byte) : 0 ||| x = x := BitVec.zero_or

/-- Bytes before `M'`'s place are as in `V`. -/
theorem vLen_lt (V : Nat → Byte) (len : List Byte) (B L fb : Nat) :
    ∀ n o, o < oY → vLen V len B L fb n o = V o
  | 0, _, _ => rfl
  | n + 1, o, h => by
    simp only [vLen]
    rw [ifn (by omega_using [h]), vLen_lt V len B L fb n o h]

/-- `M'` after its `0x80` and its length field: the padded message, over
its first `fb + 1` blocks. -/
theorem y_pad {B L fb nbm : Nat} (msg len : List Byte) (hfb : fb = lastBlk B L msg.length) (hLB : L < B)
    (hfbn : fb < nbm) (W : Nat → Byte)
    (hW : ∀ j < B * nbm, W (oY + j) = msg.getD j 0 ||| (if j = msg.length then 0x80 else 0)) :
    ∀ j < B * (fb + 1), vLen W len B L fb nbm (oY + j) = padded B L msg len j := by
  intro j hj
  obtain hB0 : 0 < B := by omega_using [hLB]
  obtain e := Nat.div_add_mod j B
  obtain hk : j % B < B := Nat.mod_lt _ hB0
  obtain hb : j / B < fb + 1 := (Nat.div_lt_iff_lt_mul hB0).mpr (by rw [Nat.mul_comm]; exact hj)
  obtain hfit : msg.length + L < B * (fb + 1) := by
    rw [hfb]; unfold lastBlk
    have := Nat.lt_div_mul_add (a := msg.length + L) (b := B) hB0
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega_using [this]
  obtain hlow : B * fb ≤ msg.length + L := by rw [hfb]; unfold lastBlk; exact Nat.mul_div_le _ _
  obtain hjn : j < B * nbm := Nat.lt_of_lt_of_le hj (Nat.mul_le_mul_left _ hfbn)
  generalize hbv : j / B = b at e hb
  generalize hkv : j % B = k at e hk
  subst e
  rw [show oY + (B * b + k) = oY + B * b + k by omega_using [], vLen_at W len fb (Nat.le_of_lt hLB) nbm (by omega_using [hfbn, hb]) hk,
    show oY + B * b + k = oY + (B * b + k) by omega_using [], hW _ hjn]
  simp only [padded, ← hfb]
  rw [Nat.mul_add, Nat.mul_one] at hfit hj
  obtain hz : ∀ i, msg.length ≤ i → msg.getD i 0 = 0 := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl
  by_cases e₁ : B * b + k < msg.length
  · have : ¬(b = fb ∧ B - L ≤ k) := by
      rintro ⟨rfl, _⟩; omega_arith
    rw [ifn (by omega_using [e₁]), ifn this, ifp e₁, or0, or0]
  · rw [hz _ (by omega_using [e₁]), ifn e₁]
    by_cases e₂ : B * b + k = msg.length
    · have : ¬(b = fb ∧ B - L ≤ k) := by
        rintro ⟨rfl, _⟩; omega_arith
      rw [ifp e₂, ifn this, ifp e₂, or0, zor]
    · rw [ifn e₂, ifn e₂]
      by_cases e₃ : b = fb
      · subst e₃
        by_cases e₄ : B - L ≤ k
        · rw [ifp ⟨rfl, e₄⟩, ifp ⟨by omega_using [hLB, hB0, hk, hjn, hbv, hkv, e₁, e₂, hfb, hfbn, hfit, hlow, hb, hj, e₄], by omega_using [hLB, hB0, hk, hjn, hbv, hkv, e₁, e₂, hfb, hfbn, hfit, hlow, hb, hj, e₄]⟩, show B * b + k - (B * b + B - L) = k - (B - L) by omega_using [hLB, hB0, hk, hjn, hbv, hkv, e₁, e₂, hfb, hfbn, hfit, hlow, hb, hj, e₄]]
          rw [or0, zor]
        · rw [ifn (fun h => e₄ h.2), ifn (by omega_using [hLB, hB0, hk, hjn, hbv, hkv, e₁, e₂, hfb, hfbn, hfit, hlow, hb, hj, e₄]), or0, or0]
      · have hbf : b < b + 1 := Nat.lt_succ_self b
        have : B * (b + 1) ≤ B * fb := Nat.mul_le_mul_left _ (by omega_using [hfb, hfbn, hfit, hlow, hb, hj, hjn, hbv, hkv, e₁, e₂, e₃, hbf])
        rw [Nat.mul_succ] at this
        rw [ifn (fun h => e₃ h.1), ifn (by omega_using [hfb, hLB, hfbn, hB0, hfit, hlow, hb, hk, hj, hjn, hbv, hkv, e₁, e₂, e₃, hbf, this]), or0, or0]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : Proof.Hmac.Stream.PPC64LE.HashOK H)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j Sp s p)
  {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
include L hH T ok hl

/-- `ctHash`: from `M'` of `8 + hLen + sl` bytes at `oY`, followed by zeros
up to 2048 bytes, with the salt's length `sl` in `r25`, its digest at
`oDig`; our part of the working space before the streaming state is kept. -/
theorem ctHash_ok (hD : H.D = D) (hN : H.N = P.N) (hB : H.B = P.B) {t : State} (h : Base Sp (vP D) s t)
    (sy : t.syms = s.syms) {sl : Nat} (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) (hsl : sl < dN) {msg : List Byte}
    (hml : msg.length = 8 + D + sl) (hY : ∀ i < 2048, view t.mem (Sp s) (oY + i) = msg.getD i 0) :
    WP isa (ctHash H P f j) t fun t' => (Base Sp (vP D) s t' ∧ t'.gpr .r24 = t.gpr .r24 ∧
      (∀ o < oSt, view t'.mem (Sp s) o = view t.mem (Sp s) o) ∧
      ∀ i < D, view t'.mem (Sp s) (oDig + i) = (hH.SH.H.hash msg).getD i 0) ∧ t'.syms = s.syms := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  have hY' : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hSl : oSel = 4800 := rfl
  have hLn : oLen = 4608 := rfl
  have hDg : oDig = 1280 := rfl
  have hW' : oW = 1352 := rfl
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hNd := ok.dims.N
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  obtain hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hD0 := L.D0
  have hDN : D ≤ P.N := hl.DN
  obtain hLB : P.L < P.B := by rcases hBd with e | e <;> omega_using [hLd, e]
  obtain hB0 : 0 < P.B := by omega_using [hBd]
  obtain hS : H.S = P.N + P.B := by simp only [Hash.S, hN, hB]
  -- The lengths.
  let ℓ := 8 + D + sl
  let nbm := (dN + (8 + D - 1 + P.L)) / P.B + 1
  let fb := lastBlk P.B P.L ℓ
  obtain hnb : nbm * P.B ≤ 2048 := by
    have := Nat.div_mul_le_self (dN + (8 + D - 1 + P.L)) P.B
    rw [Nat.add_mul, Nat.one_mul]; rcases hBd with e | e <;> rw [e] at this ⊢ <;> omega_using [hLd, hk, hk2]
  obtain hn0 : 0 < nbm * P.B := Nat.mul_pos (Nat.succ_pos _) hB0
  obtain hfb : fb < nbm := by
    show (ℓ + P.L) / P.B < _ + 1
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega_using [hsl]))
  obtain hn32 : nbm ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega_using [hnb]
  obtain hcm : nbm * P.B = P.B * nbm := Nat.mul_comm _ _
  obtain hfbB : P.B * (fb + 1) ≤ 2048 := Nat.le_trans (Nat.mul_le_mul_left _ hfb) (by rw [← hcm]; exact hnb)
  refine WP.seq (WP.of_syms (wp_addi (h := by omega_using [hD, hD64]) fun t₁ o₁ e₁ => wp_addi (h := by omega_using [hD, hBd, hLd, hk, hD64, hD0, hDN, hLB, hB0, hnb, hn0, hcm, hfbB]) fun t₂ o₂ e₂ =>
    wp_lsr (h := by omega_using [hlg7]) fun t₃ o₃ e₃ => wp_addi (h := by decide) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  obtain k₄ : Only [.r29, .r28] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  obtain g29 : t₄.gpr .r29 = BitVec.ofNat 64 ℓ := by
    rw [o₄.get .r29, o₃.get .r29, o₂.get .r29, e₁, h25, hD, BitVec.ofNat_add_ofNat]; congr 1; omega_using []
  obtain g28 : t₄.gpr .r28 = BitVec.ofNat 64 nbm := by
    rw [e₄, e₃, e₂, o₁.get .r21, h.pdb, L.hdb, hD, BitVec.ofNat_add_ofNat, Proof.MdStream.PPC64LE.ofNat_shr (by omega_using [hsl, hNd, hBd, hLd, hk, hk2, hD64, hD0, hDN, hLB, hB0, hnb, hn0, hcm, hfbB]),
      hlg, BitVec.ofNat_add_ofNat]
  obtain b₄ := h.only F k₄
  -- `init`.
  refine WP.seq (WP.mono (hInit_ok F hH T b₄ (y₄.trans sy)) fun t₅ ⟨⟨b₅, g₅, s₅, r₅⟩, y₅⟩ => ?_)
  obtain iv₅ : md.stateAt t₅.mem (off (Sp s) oSt) = iv := by
    have := (hl.repr _ _ _ r₅).1
    rw [this, List.length_nil, Nat.zero_div, Md.compressList_zero]
  -- `0x80`.
  refine WP.seq (WP.of_syms (WP.mono (pad80_ok L hlg hlg7 b₅ (ℓ := ℓ) (by rw [g₅ _ (by decide), g28])
    (by rw [g₅ _ (by decide), g29]) hnb hn0 (by omega)) fun t₆ ⟨b₆, k₆, v₆⟩ y₆ => ?_))
  -- The length field.
  refine WP.seq (WP.of_syms (WP.mono (lenField_ok L ok.shape ok.lenLr (by rcases hBd with e | e <;> omega_using [hLn, hNd, e]) hLd.2 hlg7 (ℓ := ℓ)
    b₆ (by rw [k₆.get .r29, g₅ _ (by decide), g29]) (by omega)) fun t₇ ⟨b₇, k₇, g27, m₇⟩ y₇ => ?_))
  rw [md.lenOf_eq _ (ok.lenOk _ (by omega))] at m₇
  obtain g27' : t₇.gpr .r27 = BitVec.ofNat 64 fb := by rw [g27, hlg]; rfl
  -- Into the last block.
  obtain v₇ : ∀ o < oRsa, view t₇.mem (Sp s) o =
      if oLen ≤ o ∧ o < oLen + P.L then (md.lenBytes ℓ).getD (o - oLen) 0 else view t₆.mem (Sp s) o := by
    intro o ho; rw [m₇, view_wb _ _ (by rw [md.lenBytes_length]; omega_using [hR, hLn, hLd]) ho, md.lenBytes_length]
  refine WP.seq (WP.of_syms (WP.mono (lenLoop_ok L hBd hLB hLd.1 b₇
    (by rw [k₇.get .r28, k₆.get .r28, g₅ _ (by decide), g28]) g27' (by omega_using [hfb]) hnb (by omega_using [hfb, hn32])
    (len := md.lenBytes ℓ) (fun i hi => by rw [v₇ _ (by omega_using [hR, hLn, hLd, hi]), ifp ⟨by omega_using [], by omega_using [hi]⟩, Nat.add_sub_cancel_left]))
    fun t₈ ⟨b₈, k₈, v₈⟩ y₈ => ?_))
  -- The compression.
  obtain hst₈ : md.stateAt t₈.mem (off (Sp s) oSt) = iv := by
    rw [← iv₅]
    refine md.stateAt_congr fun i hi => ?_
    obtain e8 := v₈ (oSt + i) (by omega_using [hR, hSt, hNd, hi])
    rw [vLen_lt _ _ _ _ _ _ _ (by omega_using [hY', hSt, hNd, hi]), v₇ _ (by omega_using [hR, hSt, hNd, hi]), ifn (by omega_using [hSt, hLn, hNd, hBd, hLd, hDN, hLB, hB0, hnb, hn0, hcm, hfbB, hi]), v₆ _ (by omega_using [hR, hSt, hNd, hi])] at e8
    simp only [v80] at e8
    rw [ifn (by omega_using [hY', hSt, hNd, hBd, hLd, hDN, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, hi])] at e8
    rw [off_add']; exact e8
  refine WP.seq (WP.mono (compLoop_ok L T ok b₈ (y₈.trans (y₇.trans (y₆.trans y₅)))
    (by rw [k₈.get .r28, k₇.get .r28, k₆.get .r28, g₅ _ (by decide), g28])
    (by rw [k₈.get .r27, g27']) (Nat.succ_pos _) hnb hfb) fun t₉ I => ?_)
  rw [hst₈] at I
  -- The digest.
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun t₁₀ o₁₀ e₁₀ => wp_addi (h := by decide)
    fun t₁₁ o₁₁ e₁₁ => wp_nil fun y₁₁ => ?_))
  obtain k₁₁ : Only [.r3, .r4] t₉ t₁₁ := (o₁₀.trans o₁₁).mono
  refine WP.mono (digM_ok F T ok.dig ok.digNF hNd.2 (I.base.only F k₁₁) (y₁₁.trans I.sy)
    (by rw [o₁₁.get .r3, e₁₀, I.base.r14]) (by rw [e₁₁, o₁₀.get .r14, I.base.r14])) fun t' ⟨⟨b', g', s', m'⟩, y'⟩ =>
    ⟨⟨b', ?_, fun o ho => ?_, fun i hi => ?_⟩, y'⟩
  · rw [g' _ (by decide), k₁₁.get .r24, I.keep .r24 (by simp), k₈.get .r24, k₇.get .r24, k₆.get .r24,
      g₅ _ (by decide), k₄.get .r24]
  · rw [s' o (by omega_using [hR, hSt, ho]) (by simp; omega_using [hSt, hDg, ho]), show view t₁₁.mem (Sp s) o = view t₉.mem (Sp s) o by rw [k₁₁.mem],
      I.mem o (by omega_using [hR, hSt, ho]) (.inl ho), v₈ o (by omega_using [hR, hSt, ho]), vLen_lt _ _ _ _ _ _ _ (by omega_using [hY', hSt, ho]), v₇ o (by omega_using [hR, hSt, ho]),
      ifn (by omega_using [hSt, hLn, ho]), v₆ o (by omega_using [hR, hSt, ho])]
    simp only [v80]
    rw [ifn (by omega_using [hY', hSt, hBd, hLd, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, ho]), s₅ o (by omega_using [hR, hSt, ho]) (by simp; omega_using [ho]), show view t₄.mem (Sp s) o = view t.mem (Sp s) o by
      rw [k₄.mem]]
  · -- The selected hash value is that of the padded message.
    obtain hsel := I.sel hfb
    obtain hpad : md.compressList iv (yl (view t₈.mem (Sp s))) (fb + 1) =
        md.compressList iv (md.pad msg) ((md.pad msg).length / P.B) := by
      rw [RsaPss.pad_length md msg hB0 hLB, Nat.mul_div_cancel_left _ hB0, hml]
      refine md.compressList_congr fun j hj => ?_
      rw [RsaPss.pad_getD md msg hB0 hLB (by rw [hml]; exact hj), yl_getD (by omega_using [hfbB, hj]), v₈ _ (by omega_using [hR, hY', hfbB, hj])]
      refine (y_pad msg _ (by rw [hml]) hLB hfb _ (fun j' hj' => ?_) j hj).trans (by rw [hml])
      rw [v₇ _ (by omega_using [hR, hY', hBd, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, hj, hj']), ifn (by omega_using [hY', hLn, hBd, hLd, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, hj, hj']), v₆ _ (by omega_using [hR, hY', hBd, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, hj, hj'])]
      simp only [v80]
      rw [ifp ⟨by omega_using [], by omega_using [hcm, hj']⟩, Nat.add_sub_cancel_left, s₅ _ (by omega_using [hR, hY', hBd, hLB, hB0, hnb, hn0, hfb, hn32, hcm, hfbB, hj, hj']) (by simp; omega_using [hY', hSt, hNd, hBd, hDN, hLB, hB0, hS, hnb, hn0, hfb, hn32, hcm, hfbB, hj, hj']),
        show view t₄.mem (Sp s) (oY + j') = view t.mem (Sp s) (oY + j') by rw [k₄.mem], hY j' (by omega_using [hnb, hcm, hj']), hml]
    obtain hdl := md.digest_length (md.stateAt t₁₁.mem (off (Sp s) oSel))
    rw [m', view_wb _ _ (by rw [hdl]; omega_using [hR, hDg, hNd]) (by omega_using [hR, hDg, hD64, hi]), ifp ⟨by omega_using [], by rw [hdl]; omega_using [hDN, hi]⟩, Nat.add_sub_cancel_left,
      k₁₁.mem, hsel, hpad, hl.hash]
    show (md.hash iv msg).getD i 0 = ((md.hash iv msg).take D).getD i 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

end

end VG.Proof.RsaPss.PPC64LE
