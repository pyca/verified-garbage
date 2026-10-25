module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: the shift

Untrusted: everything here is checked by Lean. `shiftPass_ok`: a pass of
the shift on `DB`'s place in `M'`, by bit 0 of `r8`, by `r9` bytes
(`passV`); `shift_ok`: the ten passes, by the bits of `pos + 1` (`shV`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_xor wp_and wp_lsr
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- `-(x ∧ 1)`: all ones if `x` is odd, zero if not. -/
theorem mask_odd (x : Nat) : BitVec.ofNat 64 0 - (BitVec.ofNat 64 x &&& BitVec.ofNat 64 1) =
    if x % 2 = 1 then BitVec.allOnes 64 else 0#64 := by
  have e : BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
    have := Nat.mod_lt x (show 0 < 2 by decide)
    rw [Nat.mod_eq_of_lt (by omega_arith : x % 2 < 2 ^ 64)]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

/-- The byte a pass writes: `a ⊕ ((b ⊕ a) ∧ m)`, for the mask `m`. -/
theorem sel_byte (a b : Byte) (bit : Bool) :
    ((a.setWidth 64 ^^^ ((b.setWidth 64 ^^^ a.setWidth 64) &&&
      (if bit then BitVec.allOnes 64 else 0#64))).setWidth 8) = if bit then b else a := by
  cases bit
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_comm (a.setWidth 64)]
    simp [BitVec.xor_assoc]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- A pass, by bit 0 of `x` (`r8`) and `d` bytes (`r9`). -/
theorem shiftPass_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    {x d : Nat} (h8 : t.gpr .r8 = BitVec.ofNat 64 x) (h9 : t.gpr .r9 = BitVec.ofNat 64 d) (hd : d ≤ 512) :
    WP isa (shiftPass H) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r11] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = passV (view t.mem (Sp s)) (oY + 8 + D) dN (x % 2 = 1) d o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hd1 := L.d1
  have hY : oY = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  let b := oY + 8 + D
  let V := view t.mem (Sp s)
  let bit : Bool := x % 2 = 1
  refine WP.seq (wp_addi (h := by rw [hD]; unfold oY; omega_arith) fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ =>
    wp_sub fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r4, .r5, .r6, .r7] t t₇ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have a4 : t₁.gpr .r4 = off (Sp s) b := by rw [e₁, h.r14, hD]
  have g6 : t₇.gpr .r6 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .r6, e₆, e₅, o₅.get .r6, e₄, e₃, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8, mask_odd]
    simp only [bit, decide_eq_true_eq]
  have g7 : t₇.gpr .r7 = BitVec.ofNat 64 dN := by
    rw [e₇, o₆.get .r21, o₅.get .r21, o₄.get .r21, o₃.get .r21, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb]
  have W : ∀ i, (fun o => if b ≤ o ∧ o < b + i then (if bit then V (o + d) else V o) else V o) =
      fun o => if b ≤ o ∧ o < b + i then (if bit then V (o + d) else V o) else V o := fun _ => rfl
  refine WP.mono (wp_countdown (cnt := .r7) (N := dN) (by omega_arith) (by omega_arith)
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r3, .r4, .r5, .r7, .r11] t₇ u ∧ u.gpr .r4 = off (Sp s) (b + i) ∧
      u.gpr .r5 = off (Sp s) (b + i + d) ∧ ∀ o < oRsa, view u.mem (Sp s) o =
        if b ≤ o ∧ o < b + i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨h.only F k₇, Keep.refl _ _, by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, a4]; rfl,
      by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, a4, o₁.get .r9, h9]; exact off_off _ _ _,
      fun o _ => by rw [ifn (by omega_arith), k₇.mem]⟩ g7) fun u ⟨bu, ou, _, _, vu⟩ =>
    ⟨bu, (k₇.keep.trans ou).mono, fun o ho => by rw [vu o ho]; rfl⟩
  intro i hi u ⟨bu, ou, u4, u5, vu⟩ _
  refine wp_lbz (a := off (Sp s) (b + i)) (by rw [u4, BitVec.add_zero])
    (by rw [bu.wr]; exact sc_inR F (by omega_arith) _) fun u₁ p₁ f₁ => ?_
  refine wp_lbz (a := off (Sp s) (b + i + d)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR F (by omega_arith) _) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.r11, .r3] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_stb (a := off (Sp s) (b + i)) (by rw [k₅.get .r4, u4, BitVec.add_zero])
    (by rw [k₅.wr, bu.wr]; exact sc_inW F (by omega_arith)) fun u₆ m₆ => ?_
  refine wp_addi fun u₇ p₇ f₇ => wp_addi fun u₈ p₈ f₈ => wp_subi fun u₉ p₉ f₉ => wp_nil ?_
  have hm0 : u₅.mem = u.mem := k₅.mem
  have hb : (u₅.gpr .r11).setWidth 8 = if bit then V (b + i + d) else V (b + i) := by
    have va : u.mem (off (Sp s) (b + i)) = V (b + i) := by
      have := vu (b + i) (by omega_arith); rw [ifn (by omega_arith)] at this; exact this
    have vb : u₁.mem (off (Sp s) (b + i + d)) = V (b + i + d) := by
      have := vu (b + i + d) (by omega_arith); rw [ifn (by omega_arith)] at this; rw [p₁.mem]; exact this
    rw [f₅, p₄.get .r11, p₃.get .r11, p₂.get .r11, f₁, f₄, f₃, f₂, p₂.get .r11, f₁, va, vb, p₃.get .r6,
      p₂.get .r6, p₁.get .r6, ou.get .r6, g6]
    exact sel_byte _ _ bit
  have q : Keep [.r11, .r3, .r4, .r5, .r7] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (off (Sp s) (b + i)) (if bit then V (b + i + d) else V (b + i)) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, hm0]
  refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (b + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega_arith))),
    ?_, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · exact (ou.trans q).mono
  · rw [p₉.get .r4, p₈.get .r4, f₇, m₆.gpr, k₅.get .r4, u4]; exact off_off _ _ _
  · rw [p₉.get .r5, f₈, p₇.get .r5, m₆.gpr, k₅.get .r5, u5]
    show off (off (Sp s) (b + i + d)) 1 = off (Sp s) (b + (i + 1) + d)
    rw [off_off, show b + i + d + 1 = b + (i + 1) + d by omega_arith]
  · rw [hm, view_w8 _ _ (by omega_arith) ho, vu o ho]
    by_cases e : o = b + i
    · subst e
      rw [ifp (show b + i = b + i from rfl), ifp (show b ≤ b + i ∧ b + i < b + (i + 1) from ⟨by omega_arith, by omega_arith⟩)]
    · rw [ifn e]
      by_cases e' : b ≤ o ∧ o < b + i
      · rw [ifp e', ifp (show b ≤ o ∧ o < b + (i + 1) from ⟨e'.1, by omega_arith⟩)]
      · rw [ifn e', ifn (show ¬(b ≤ o ∧ o < b + (i + 1)) by omega_arith)]
  · rw [f₉, p₈.get .r7, p₇.get .r7, m₆.gpr, k₅.get .r7]

/-- The shift: `DB`'s place in `M'` by `pos + 1`, from `pos` in `r8`. -/
theorem shift_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    {pos : Nat} (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN) :
    WP isa (shift H) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = shV (view t.mem (Sp s)) (oY + 8 + D) dN (pos + 1) 10 o := by
  have hk := L.hk; have hk2 := L.k2
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r8, .r9, .r10] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  let V := view t.mem (Sp s)
  refine WP.mono (wp_countdown (cnt := .r10) (N := 10) (by decide) (by decide)
    (fun j u => Base Sp (vP D) s u ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] t u ∧
      u.gpr .r8 = BitVec.ofNat 64 ((pos + 1) / 2 ^ j) ∧ u.gpr .r9 = BitVec.ofNat 64 (2 ^ j) ∧
      ∀ o < oRsa, view u.mem (Sp s) o = shV V (oY + 8 + D) dN (pos + 1) j o) ?_
    ⟨h.only L.F k₃, k₃.keep.mono, by rw [o₃.get .r8, o₂.get .r8, e₁, h8, ← BitVec.ofNat_add, Nat.pow_zero, Nat.div_one],
      by rw [o₃.get .r9, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, ku, vu⟩
  intro j hj u ⟨bu, ku, u8, u9, vu⟩ _
  have hp9 : 2 ^ j ≤ 512 := by
    have : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    exact this
  refine WP.seq (WP.mono (shiftPass_ok L hD bu u8 u9 hp9) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  refine wp_lsr fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_nil ?_
  have k₄ : Only [.r8, .r9, .r10] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨b₁.only L.F k₄, (ku.trans (k₁.trans k₄.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .r8, p₃.get .r8, f₂, k₁.get .r8, u8, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : (pos + 1) / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self (pos + 1) (2 ^ j); omega_arith
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self ((pos + 1) / 2 ^ j) 2; omega_arith)]
  · rw [p₄.get .r9, f₃, p₂.get .r9, k₁.get .r9, u9, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄.mem, v₁ o ho]
    show passV (view u.mem (Sp s)) _ _ _ _ o = passV (shV V (oY + 8 + D) dN (pos + 1) j) _ _ _ _ o
    unfold passV
    have e : ∀ o' < oRsa, view u.mem (Sp s) o' = shV V (oY + 8 + D) dN (pos + 1) j o' := vu
    by_cases c : oY + 8 + D ≤ o ∧ o < oY + 8 + D + dN
    · have hR : oRsa = 8192 := rfl
      have hY : oY = 2560 := rfl
      have := L.D64
      rw [ifp c, ifp c, e o ho, e (o + 2 ^ j) (by omega_arith)]
    · rw [ifn c, ifn c, e o ho]
  · rw [f₄, p₃.get .r10, p₂.get .r10, k₁.get .r10]

end

end VG.Proof.RsaPss.PPC64LE
