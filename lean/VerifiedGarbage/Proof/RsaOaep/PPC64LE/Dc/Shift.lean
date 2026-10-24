module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Buf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV

/-!
# RSAES-OAEP decryption on PPC64LE: the shift

Untrusted: everything here is checked by Lean. As for RSASSA-PSS
verification (`Proof/RsaPss/PPC64LE/Shift.lean`): `shiftPass_ok`, a pass
over the buffer's first `k` bytes by one bit of `idx + 1` (`passV`), and
`shift_ok`, ten of them (`shV`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_lsr
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.RsaPss.PPC64LE (passV shV)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- A pass, by bit 0 of `x` (`r8`) and `d` bytes (`r9`). -/
theorem shiftPass_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t)
    {x d : Nat} (h8 : t.gpr .r8 = BitVec.ofNat 64 x) (h9 : t.gpr .r9 = BitVec.ofNat 64 d) (hd : d ≤ 512) :
    WP isa shiftPass t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r11] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = passV (view t.mem (Sd s)) oBuf (kk s) (x % 2 = 1) d o := by
  have PF := fitsM (m := m) P
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  let V := view t.mem (Sd s)
  let bit : Bool := x % 2 = 1
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ =>
    wp_sub fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r4, .r5, .r6, .r7] t t₇ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have a4 : t₁.gpr .r4 = off (Sd s) oBuf := by rw [e₁, h.r14]
  have g6 : t₇.gpr .r6 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .r6, e₆, e₅, o₅.get .r6, e₄, e₃, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8, mask_odd]
    simp only [bit, decide_eq_true_eq]
  have g7 : t₇.gpr .r7 = BitVec.ofNat 64 (kk s) := by
    rw [e₇, o₆.get .r15, o₅.get .r15, o₄.get .r15, o₃.get .r15, o₂.get .r15, o₁.get .r15, Base.r15 h]
    exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  refine WP.mono (wp_countdown (cnt := .r7) (N := kk s) (by omega) (by have := P.k1; omega)
    (fun i u => Base (SD s) (VD s rc) (withMem s m) u ∧ Keep [.r3, .r4, .r5, .r7, .r11] t₇ u ∧
      u.gpr .r4 = off (Sd s) (oBuf + i) ∧ u.gpr .r5 = off (Sd s) (oBuf + i + d) ∧ ∀ o < oRsa, view u.mem (Sd s) o =
        if oBuf ≤ o ∧ o < oBuf + i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨h.only PF k₇, Keep.refl _ _, by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, a4]; rfl,
      by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, a4, o₁.get .r9, h9]; exact off_off _ _ _,
      fun o _ => by rw [ifn (by omega), k₇.mem]⟩ g7) fun u ⟨bu, ou, _, _, vu⟩ =>
    ⟨bu, (k₇.keep.trans ou).mono, fun o ho => by rw [vu o ho]; rfl⟩
  intro i hi u ⟨bu, ou, u4, u5, vu⟩ _
  refine wp_lbz (a := off (Sd s) (oBuf + i)) (by rw [u4, BitVec.add_zero])
    (by rw [bu.wr]; exact sc_inR PF (by omega) _) fun u₁ p₁ f₁ => ?_
  refine wp_lbz (a := off (Sd s) (oBuf + i + d)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR PF (by omega) _) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.r11, .r3] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_stb (a := off (Sd s) (oBuf + i)) (by rw [k₅.get .r4, u4, BitVec.add_zero])
    (by rw [k₅.wr, bu.wr]; exact sc_inW PF (by omega)) fun u₆ m₆ => ?_
  refine wp_addi fun u₇ p₇ f₇ => wp_addi fun u₈ p₈ f₈ => wp_subi fun u₉ p₉ f₉ => wp_nil ?_
  have hm0 : u₅.mem = u.mem := k₅.mem
  have hb : (u₅.gpr .r11).setWidth 8 = if bit then V (oBuf + i + d) else V (oBuf + i) := by
    have va : u.mem (off (Sd s) (oBuf + i)) = V (oBuf + i) := by
      have := vu (oBuf + i) (by omega); rw [ifn (by omega)] at this; exact this
    have vb : u₁.mem (off (Sd s) (oBuf + i + d)) = V (oBuf + i + d) := by
      have := vu (oBuf + i + d) (by omega); rw [ifn (by omega)] at this; rw [p₁.mem]; exact this
    rw [f₅, p₄.get .r11, p₃.get .r11, p₂.get .r11, f₁, f₄, f₃, f₂, p₂.get .r11, f₁, va, vb, p₃.get .r6,
      p₂.get .r6, p₁.get .r6, ou.get .r6, g6]
    exact sel_byte _ _ bit
  have q : Keep [.r11, .r3, .r4, .r5, .r7] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (off (Sd s) (oBuf + i)) (if bit then V (oBuf + i + d) else V (oBuf + i)) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, hm0]
  refine ⟨⟨bu.keep PF q (R := [⟨off (Sd s) (oBuf + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    ?_, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · exact (ou.trans q).mono
  · rw [p₉.get .r4, p₈.get .r4, f₇, m₆.gpr, k₅.get .r4, u4]; exact off_off _ _ _
  · rw [p₉.get .r5, f₈, p₇.get .r5, m₆.gpr, k₅.get .r5, u5]
    show off (off (Sd s) (oBuf + i + d)) 1 = off (Sd s) (oBuf + (i + 1) + d)
    rw [off_off, show oBuf + i + d + 1 = oBuf + (i + 1) + d by omega]
  · rw [hm, view_w8 _ _ (by omega) ho, vu o ho]
    by_cases e : o = oBuf + i
    · subst e
      rw [ifp (show oBuf + i = oBuf + i from rfl),
        ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + (i + 1) from ⟨by omega, by omega⟩)]
    · rw [ifn e]
      by_cases e' : oBuf ≤ o ∧ o < oBuf + i
      · rw [ifp e', ifp (show oBuf ≤ o ∧ o < oBuf + (i + 1) from ⟨e'.1, by omega⟩)]
      · rw [ifn e', ifn (show ¬(oBuf ≤ o ∧ o < oBuf + (i + 1)) by omega)]
  · rw [f₉, p₈.get .r7, p₇.get .r7, m₆.gpr, k₅.get .r7]

/-- The shift: the buffer's first `k` bytes by `idx + 1`, from `idx` in `r25`. -/
theorem shift_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) {idx : Nat}
    (h25 : t.gpr .r25 = BitVec.ofNat 64 idx) (hp : idx < 1023) :
    WP isa shift t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = shV (view t.mem (Sd s)) oBuf (kk s) (idx + 1) 10 o := by
  have PF := fitsM (m := m) P
  have hk2 := P.k2
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r8, .r9, .r10] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  let V := view t.mem (Sd s)
  refine WP.mono (wp_countdown (cnt := .r10) (N := 10) (by decide) (by decide)
    (fun j u => Base (SD s) (VD s rc) (withMem s m) u ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] t u ∧
      u.gpr .r8 = BitVec.ofNat 64 ((idx + 1) / 2 ^ j) ∧ u.gpr .r9 = BitVec.ofNat 64 (2 ^ j) ∧
      ∀ o < oRsa, view u.mem (Sd s) o = shV V oBuf (kk s) (idx + 1) j o) ?_
    ⟨h.only PF k₃, k₃.keep.mono, by rw [o₃.get .r8, o₂.get .r8, e₁, h25, ← BitVec.ofNat_add, Nat.pow_zero,
      Nat.div_one], by rw [o₃.get .r9, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, ku, vu⟩
  intro j hj u ⟨bu, ku, u8, u9, vu⟩ _
  have hp9 : 2 ^ j ≤ 512 := by
    have : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  refine WP.seq (WP.mono (shiftPass_ok P bu u8 u9 hp9) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  refine wp_lsr fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_nil ?_
  have k₄ : Only [.r8, .r9, .r10] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨b₁.only PF k₄, (ku.trans (k₁.trans k₄.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .r8, p₃.get .r8, f₂, k₁.get .r8, u8, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : (idx + 1) / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self (idx + 1) (2 ^ j); omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self ((idx + 1) / 2 ^ j) 2; omega)]
  · rw [p₄.get .r9, f₃, p₂.get .r9, k₁.get .r9, u9, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄.mem, v₁ o ho]
    show passV (view u.mem (Sd s)) _ _ _ _ o = passV (shV V oBuf (kk s) (idx + 1) j) _ _ _ _ o
    unfold passV
    have e : ∀ o' < oRsa, view u.mem (Sd s) o' = shV V oBuf (kk s) (idx + 1) j o' := vu
    by_cases c : oBuf ≤ o ∧ o < oBuf + kk s
    · have hR : oRsa = 8192 := rfl
      have hB : oBuf = 2560 := rfl
      have ek : kk s = (s.gpr .r7).toNat := rfl
      rw [ifp c, ifp c, e o ho, e (o + 2 ^ j) (by omega)]
    · rw [ifn c, ifn c, e o ho]
  · rw [f₄, p₃.get .r10, p₂.get .r10, k₁.get .r10]

end

end VG.Proof.RsaOaep.PPC64LE.Dec
