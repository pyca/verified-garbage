module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS verification on RISC-V: the shift

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Shift.lean`): `shiftPass_ok`: a pass of
the shift on `DB`'s place in `M'`, by bit 0 of `s8`, by `s9` bytes
(`passV`); `shift_ok`: the ten passes, by the bits of `pos + 1` (`shV`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_xor wp_and wp_srl
  wp_lbu wp_sb wp_nil)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- `-(x ∧ 1)`: all ones if `x` is odd, zero if not. -/
theorem mask_odd (x : Nat) : BitVec.ofNat 64 0 - (BitVec.ofNat 64 x &&& BitVec.ofNat 64 1) =
    if x % 2 = 1 then BitVec.allOnes 64 else 0#64 := by
  have e : BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
    have := Nat.mod_lt x (show 0 < 2 by decide)
    rw [Nat.mod_eq_of_lt (by omega : x % 2 < 2 ^ 64)]
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

/-- A pass, by bit 0 of `x` (`s8`) and `d` bytes (`s9`). -/
theorem shiftPass_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    {x d : Nat} (h8 : t.gpr .s8 = BitVec.ofNat 64 x) (h9 : t.gpr .s9 = BitVec.ofNat 64 d) (hd : d ≤ 512) :
    WP isa (shiftPass H) t fun t' => Base Sp (vP D) s t' ∧ Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = passV (view t.mem (Sp s)) (oY + 8 + D) dN (x % 2 = 1) d o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hd1 := L.d1
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  let b := oY + 8 + D
  let V := view t.mem (Sp s)
  let bit : Bool := x % 2 = 1
  refine WP.seq (wp_yBase h.s0 fun t₀ o₀ e₀ => wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun t₁ o₁ e₁ =>
    wp_add fun t₂ o₂ e₂ => wp_li (imm := 1) (by decide) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.a1, .a2, .a3, .a4, .a5] t t₇ :=
    (o₀.trans (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))))).mono
  have a4 : t₁.gpr .a1 = off (Sp s) b := by
    rw [e₁, e₀, hD]; exact (off_off _ _ _).trans (congrArg _ (Nat.add_assoc _ _ _).symm)
  have g6 : t₇.gpr .a3 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .a3, e₆, e₅, o₅.get .a3, e₄, e₃, o₃.get .s8, o₂.get .s8, o₁.get .s8, o₀.get .s8, h8, mask_odd]
    simp only [bit, decide_eq_true_eq]
  have g7 : t₇.gpr .a5 = BitVec.ofNat 64 dN := by
    rw [e₇, o₆.get .s4, o₅.get .s4, o₄.get .s4, o₃.get .s4, o₂.get .s4, o₁.get .s4, o₀.get .s4, h.pdb, L.hdb]
  refine WP.mono (wp_countdown (cnt := .a5) (N := dN) (by omega) (by omega)
    (fun i u => Base Sp (vP D) s u ∧ Kept [.a1, .a2, .a5, .t1, .t2] t₇ u ∧ u.gpr .a1 = off (Sp s) (b + i) ∧
      u.gpr .a2 = off (Sp s) (b + i + d) ∧ ∀ o < oRsa, view u.mem (Sp s) o =
        if b ≤ o ∧ o < b + i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨h.only F k₇, Kept.refl _ _, by rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, a4]; rfl,
      by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, a4, o₁.get .s9, o₀.get .s9, h9]
         exact off_off _ _ _,
      fun o _ => by rw [ifn (by omega), k₇.mem]⟩ g7) fun u ⟨bu, ou, _, _, vu⟩ =>
    ⟨bu, (k₇.keep.trans ou).mono, fun o ho => by rw [vu o ho]; rfl⟩
  intro i hi u ⟨bu, ou, u4, u5, vu⟩ _
  simp only [List.cons_append, List.nil_append]
  refine wp_lbu (a := off (Sp s) (b + i)) (by rw [u4, BitVec.add_zero])
    (by rw [bu.wr]; exact sc_inR F (by omega) _) fun u₁ p₁ f₁ => ?_
  refine wp_lbu (a := off (Sp s) (b + i + d)) (by rw [p₁.get .a2, u5, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR F (by omega) _) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.t1, .t2] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_sb (a := off (Sp s) (b + i)) (by rw [k₅.get .a1, u4, BitVec.add_zero])
    (by rw [k₅.wr, bu.wr]; exact sc_inW F (by omega)) fun u₆ m₆ => ?_
  refine wp_addi (imm := 1) fun u₇ p₇ f₇ => wp_addi (imm := 1) fun u₈ p₈ f₈ =>
    wp_subi (imm := 1) fun u₉ p₉ f₉ => wp_nil ?_
  have hm0 : u₅.mem = u.mem := k₅.mem
  have hb : (u₅.gpr .t1).setWidth 8 = if bit then V (b + i + d) else V (b + i) := by
    have va : u.mem (off (Sp s) (b + i)) = V (b + i) := by
      have := vu (b + i) (by omega); rw [ifn (by omega)] at this; exact this
    have vb : u₁.mem (off (Sp s) (b + i + d)) = V (b + i + d) := by
      have := vu (b + i + d) (by omega); rw [ifn (by omega)] at this; rw [p₁.mem]; exact this
    rw [f₅, p₄.get .t1, p₃.get .t1, p₂.get .t1, f₁, f₄, f₃, f₂, p₂.get .t1, f₁, va, vb, p₃.get .a3,
      p₂.get .a3, p₁.get .a3, ou.get .a3, g6]
    exact sel_byte _ _ bit
  have q : Kept [.t1, .t2, .a1, .a2, .a5] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (off (Sp s) (b + i)) (if bit then V (b + i + d) else V (b + i)) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, hm0]
  refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (b + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    ?_, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · exact (ou.trans q).mono
  · rw [p₉.get .a1, p₈.get .a1, f₇, m₆.gpr, k₅.get .a1, u4]; exact off_off _ _ _
  · rw [p₉.get .a2, f₈, p₇.get .a2, m₆.gpr, k₅.get .a2, u5]
    show off (off (Sp s) (b + i + d)) 1 = off (Sp s) (b + (i + 1) + d)
    rw [off_off, show b + i + d + 1 = b + (i + 1) + d by omega]
  · rw [hm, view_w8 _ _ (by omega) ho, vu o ho]
    by_cases e : o = b + i
    · subst e
      rw [ifp (show b + i = b + i from rfl), ifp (show b ≤ b + i ∧ b + i < b + (i + 1) from ⟨by omega, by omega⟩)]
    · rw [ifn e]
      by_cases e' : b ≤ o ∧ o < b + i
      · rw [ifp e', ifp (show b ≤ o ∧ o < b + (i + 1) from ⟨e'.1, by omega⟩)]
      · rw [ifn e', ifn (show ¬(b ≤ o ∧ o < b + (i + 1)) by omega)]
  · rw [f₉, p₈.get .a5, p₇.get .a5, m₆.gpr, k₅.get .a5]

/-- The shift: `DB`'s place in `M'` by `pos + 1`, from `pos` in `s8`. -/
theorem shift_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    {pos : Nat} (h8 : t.gpr .s8 = BitVec.ofNat 64 pos) (hp : pos < dN) :
    WP isa (shift H) t fun t' => Base Sp (vP D) s t' ∧
      Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2, .s5, .s8, .s9] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = shV (view t.mem (Sp s)) (oY + 8 + D) dN (pos + 1) 10 o := by
  have hk := L.hk; have hk2 := L.k2
  refine WP.seq (wp_addi (imm := 1) fun t₁ o₁ e₁ => wp_li (imm := 1) (by decide) fun t₂ o₂ e₂ =>
    wp_li (imm := 10) (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.s8, .s9, .s5] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  let V := view t.mem (Sp s)
  refine WP.mono (wp_countdown (cnt := .s5) (N := 10) (by decide) (by decide)
    (fun j u => Base Sp (vP D) s u ∧ Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2, .s5, .s8, .s9] t u ∧
      u.gpr .s8 = BitVec.ofNat 64 ((pos + 1) / 2 ^ j) ∧ u.gpr .s9 = BitVec.ofNat 64 (2 ^ j) ∧
      ∀ o < oRsa, view u.mem (Sp s) o = shV V (oY + 8 + D) dN (pos + 1) j o) ?_
    ⟨h.only L.F k₃, k₃.keep.mono, by rw [o₃.get .s8, o₂.get .s8, e₁, h8, ← BitVec.ofNat_add, Nat.pow_zero, Nat.div_one],
      by rw [o₃.get .s9, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, ku, vu⟩
  intro j hj u ⟨bu, ku, u8, u9, vu⟩ _
  have hp9 : 2 ^ j ≤ 512 := by
    have : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  refine WP.seq (WP.mono (shiftPass_ok L hD bu u8 u9 hp9) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  refine wp_srl fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi (imm := 1) fun u₄ p₄ f₄ => wp_nil ?_
  have k₄ : Only [.s8, .s9, .s5] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨b₁.only L.F k₄, (ku.trans (k₁.trans k₄.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .s8, p₃.get .s8, f₂, k₁.get .s8, u8, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : (pos + 1) / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self (pos + 1) (2 ^ j); omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self ((pos + 1) / 2 ^ j) 2; omega)]
  · rw [p₄.get .s9, f₃, p₂.get .s9, k₁.get .s9, u9, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄.mem, v₁ o ho]
    show passV (view u.mem (Sp s)) _ _ _ _ o = passV (shV V (oY + 8 + D) dN (pos + 1) j) _ _ _ _ o
    unfold passV
    have e : ∀ o' < oRsa, view u.mem (Sp s) o' = shV V (oY + 8 + D) dN (pos + 1) j o' := vu
    by_cases c : oY + 8 + D ≤ o ∧ o < oY + 8 + D + dN
    · have hR : oRsa = 8192 := rfl
      have hY : oY = 2048 := rfl
      have := L.D64
      rw [ifp c, ifp c, e o ho, e (o + 2 ^ j) (by omega)]
    · rw [ifn c, ifn c, e o ho]
  · rw [f₄, p₃.get .s5, p₂.get .s5, k₁.get .s5]

end

end VG.Proof.RsaPss.RISCV64
