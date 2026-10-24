module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: copies and the selection

Untrusted: everything here is checked by Lean. `copyN_ok`: `copyN a b n`
copies `n` bytes of our part of the working space from `a` to `b`;
`select_ok`: `select` copies the digest at `oDig` to `oSel` if the length
`L` (`r26`) is the salt's (`r25`), and leaves it if not, by a mask.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa copyLoop)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_sub wp_xor wp_and wp_lsr wp_lbz wp_stb
  wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- `-((L ⊕ sl) - 1 >>> 63)`: all ones if `L = sl`, zero if not, for `L, sl < 2^63`. -/
theorem eq_mask {L sl : Nat} (hL : L < 2 ^ 63) (hs : sl < 2 ^ 63) :
    BitVec.ofNat 64 0 - (((BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl) - BitVec.ofNat 64 1) >>> 63) =
      if L = sl then BitVec.allOnes 64 else 0#64 := by
  have hx : (BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact Nat.xor_lt_two_pow hL hs
  rw [isz64 hx]
  by_cases e : L = sl
  · subst e; rw [BitVec.xor_self, ifp rfl, ifp rfl]; decide
  · have : BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl ≠ 0#64 := fun h => e (by
      have := BitVec.xor_eq_zero_iff.mp h
      have := congrArg BitVec.toNat this
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
    rw [ifn this, ifn e]; decide

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `copyN a b n`. -/
theorem copyN_ok {t : State} (h : Base Sp (vP D) s t) {a b n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 15)
    (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa) (hab : a + n ≤ b ∨ b + n ≤ a) (ha' : a < 2 ^ 15) (hb' : b < 2 ^ 15) :
    WP isa (copyN a b n) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r4, .r5, .r6, .r7] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o =
        if b ≤ o ∧ o < b + n then view t.mem (Sp s) (a + (o - b)) else view t.mem (Sp s) o := by
  refine WP.seq (wp_addi (h := ha') fun t₁ o₁ e₁ => wp_addi (h := hb') fun t₂ o₂ e₂ => wp_li hn' fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copyIn_ok L (h.only L.F k₃) hn ha hb hab (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14])
    (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14]) (by rw [e₃])) fun t' ⟨b', k', v'⟩ =>
    ⟨b', (k₃.keep.trans k').mono, fun o ho => by rw [v' o ho, k₃.mem]⟩

/-- `select`: the digest at `oDig` to `oSel` if `L = sl`. -/
theorem select_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    {Ln sl : Nat} (h26 : t.gpr .r26 = BitVec.ofNat 64 Ln) (h25 : t.gpr .r25 = BitVec.ofNat 64 sl)
    (hL : Ln < 2 ^ 63) (hs : sl < 2 ^ 63) :
    WP isa (select H) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oSel ≤ o ∧ o < oSel + D ∧ Ln = sl then
        view t.mem (Sp s) (oDig + (o - oSel)) else view t.mem (Sp s) o := by
  have F := L.F
  have hD0 := L.D0; have hD64 := L.D64
  have hR : oRsa = 8192 := rfl
  have hS : oSel = 4800 := rfl
  have hDg : oDig = 1280 := rfl
  let V := view t.mem (Sp s)
  let bit : Bool := Ln = sl
  refine WP.seq (wp_xor fun t₁ o₁ e₁ => wp_subi fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_li (by decide)
    fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_addi (h := by decide) fun t₆ o₆ e₆ =>
    wp_addi (h := by decide) fun t₇ o₇ e₇ => wp_li (by rw [hD]; omega) fun t₈ o₈ e₈ => wp_nil ?_)
  have k₈ : Only [.r3, .r4, .r5, .r6] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  have g3 : t₈.gpr .r3 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₈.get .r3, o₇.get .r3, o₆.get .r3, e₅, e₄, o₄.get .r3, e₃, e₂, e₁, h26, h25, eq_mask hL hs]
    simp only [bit, decide_eq_true_eq]
  refine WP.mono (wp_countdown (cnt := .r6) (N := D) (by omega) hD0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8] t₈ u ∧ u.gpr .r4 = off (Sp s) (oDig + i) ∧
      u.gpr .r5 = off (Sp s) (oSel + i) ∧ ∀ o < oRsa, view u.mem (Sp s) o =
        if oSel ≤ o ∧ o < oSel + i then (if bit then V (oDig + (o - oSel)) else V o) else V o) ?_
    ⟨h.only F k₈, Keep.refl _ _, by rw [o₈.get .r4, o₇.get .r4, e₆, o₅.get .r14, o₄.get .r14, o₃.get .r14,
      o₂.get .r14, o₁.get .r14, h.r14]; rfl, by rw [o₈.get .r5, e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14,
      o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14]; rfl, fun o _ => by rw [ifn (by omega), k₈.mem]⟩
    (by rw [e₈, hD])) fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₈.keep.trans ku).mono, fun o ho => ?_⟩
  · intro i hi u ⟨bu, ku, u4, u5, vu⟩ _
    refine wp_lbz (a := off (Sp s) (oDig + i)) (by rw [u4, BitVec.add_zero])
      (by rw [bu.wr]; exact sc_inR F (by omega) _) fun u₁ p₁ f₁ => ?_
    refine wp_lbz (a := off (Sp s) (oSel + i)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
      (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR F (by omega) _) fun u₂ p₂ f₂ => ?_
    refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
    have k₅ : Only [.r7, .r8] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
    refine wp_stb (a := off (Sp s) (oSel + i)) (by rw [k₅.get .r5, u5, BitVec.add_zero])
      (by rw [k₅.wr, bu.wr]; exact sc_inW F (by omega)) fun u₆ m₆ => ?_
    refine wp_addi fun u₇ p₇ f₇ => wp_addi fun u₈ p₈ f₈ => wp_subi fun u₉ p₉ f₉ => wp_nil ?_
    have hb : (u₅.gpr .r8).setWidth 8 = if bit then V (oDig + i) else V (oSel + i) := by
      have va : u.mem (off (Sp s) (oDig + i)) = V (oDig + i) := by
        have := vu (oDig + i) (by omega); rw [ifn (by omega)] at this; exact this
      have vb : u₁.mem (off (Sp s) (oSel + i)) = V (oSel + i) := by
        have := vu (oSel + i) (by omega); rw [ifn (by omega)] at this; rw [p₁.mem]; exact this
      rw [f₅, p₄.get .r8, p₃.get .r8, f₂, f₄, f₃, p₂.get .r7, f₁, f₂, va, vb, p₃.get .r3, p₂.get .r3, p₁.get .r3,
        ku.get .r3, g3]
      exact sel_byte _ _ bit
    have q : Keep [.r7, .r8, .r4, .r5, .r6] u u₉ :=
      (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
    have hm : u₉.mem = u.mem.writeW (off (Sp s) (oSel + i)) (if bit then V (oDig + i) else V (oSel + i)) := by
      rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, k₅.mem]
    refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (oSel + i), 1⟩]) (by
        rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
      (ku.trans q).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
    · rw [p₉.get .r4, p₈.get .r4, f₇, m₆.gpr, k₅.get .r4, u4]; exact off_off _ _ _
    · rw [p₉.get .r5, f₈, p₇.get .r5, m₆.gpr, k₅.get .r5, u5]; exact off_off _ _ _
    · rw [hm, view_w8 _ _ (by omega) ho, vu o ho]
      by_cases e : o = oSel + i
      · subst e
        rw [ifp (show oSel + i = oSel + i from rfl),
          ifp (show oSel ≤ oSel + i ∧ oSel + i < oSel + (i + 1) from ⟨by omega, by omega⟩),
          show oDig + (oSel + i - oSel) = oDig + i by omega]
      · rw [ifn e]
        by_cases e' : oSel ≤ o ∧ o < oSel + i
        · rw [ifp e', ifp (show oSel ≤ o ∧ o < oSel + (i + 1) from ⟨e'.1, by omega⟩)]
        · rw [ifn e', ifn (show ¬(oSel ≤ o ∧ o < oSel + (i + 1)) by omega)]
    · rw [f₉, p₈.get .r6, p₇.get .r6, m₆.gpr, k₅.get .r6]
  · rw [vu o ho]
    by_cases e : oSel ≤ o ∧ o < oSel + D
    · rw [ifp e]
      by_cases eb : Ln = sl
      · rw [ifp (show oSel ≤ o ∧ o < oSel + D ∧ Ln = sl from ⟨e.1, e.2, eb⟩), ifp (by simpa [bit] using eb)]
      · rw [ifn (show ¬(oSel ≤ o ∧ o < oSel + D ∧ Ln = sl) from fun h' => eb h'.2.2), ifn (by simpa [bit] using eb)]
    · rw [ifn e, ifn (show ¬(oSel ≤ o ∧ o < oSel + D ∧ Ln = sl) from fun h' => e ⟨h'.1, h'.2.1⟩)]

end

end VG.Proof.RsaPss.PPC64LE
