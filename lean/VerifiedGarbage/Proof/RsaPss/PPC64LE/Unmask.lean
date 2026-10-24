module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base

/-!
# RSASSA-PSS verification on PPC64LE: `DB`

Untrusted: everything here is checked by Lean. `unmask_ok`: `dbArgs` (`dbArgs_ok`), MGF1
(`mgfXor_ok`, shared with RSAES-OAEP encryption) and `clearTop` (`clearTop_ok`) leave `DB` in
`EM`'s place: `maskedDB` XORed with MGF1 of `H`, its first byte ANDed with
`c` (`dbV`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa mgfXor)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs MFit mgfXor_ok)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_add wp_mov wp_and wp_lbz wp_stb wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `DB` in `EM`'s place, from its view `V` before unmasking. -/
def dbV (Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (lN dN D : Nat) (c : Byte) (o : Nat) : Byte :=
  let W := mixV V (Spec.Mgf1.mgf1 Gs (srcB V (lN + dN) D) dN) lN dN
  if o = lN then W o &&& c else W o

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- MGF1's arguments for unmasking `DB`: `H` after it as the seed. -/
theorem dbArgs_ok {H : Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block (dbArgs H)) t fun t' => Base Sp (vP D) s t' ∧ Only [.r26, .r27, .r24, .r25] t t' ∧
      t'.gpr .r24 = off (Sp s) (lN + dN) ∧ t'.gpr .r25 = BitVec.ofNat 64 D ∧ t'.gpr .r26 = off (Sp s) lN ∧
      t'.gpr .r27 = BitVec.ofNat 64 dN := by
  have F := L.F
  have hD64 := L.D64
  subst hD
  refine wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_li (by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.r26, .r27, .r24, .r25] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a26 : t₁.gpr .r26 = off (Sp s) lN := by rw [e₁, h.r14, h.plo, L.hlo]
  exact ⟨h.only F k₄, k₄,
    by rw [o₄.get .r24, e₃, o₂.get .r26, a26, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb]; exact off_off _ _ _,
    by rw [e₄], by rw [o₄.get .r26, o₃.get .r26, o₂.get .r26, a26],
    by rw [o₄.get .r27, o₃.get .r27, e₂, o₁.get .r21, h.pdb, L.hdb]⟩

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block clearTop) t fun w => Base Sp (vP D) s w ∧ Keep [.r4, .r5] t w ∧
      ∀ o < oSt, view w.mem (Sp s) o = if o = lN then view t.mem (Sp s) lN &&& c else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hl := L.l1
  have a6 : ∀ {u : State}, Only [.r4] t u → u.gpr .r4 = t.gpr .r14 + t.gpr .r17 → u.gpr .r4 = off (Sp s) lN :=
    fun o e => by rw [e, h.r14, h.plo, L.hlo]
  refine wp_add fun t₆ o₆ e₆ => ?_
  refine wp_lbz (a := off (Sp s) lN) (by rw [a6 o₆ e₆, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun t₇ o₇ e₇ => ?_
  refine wp_and fun t₈ o₈ e₈ => wp_stb (a := off (Sp s) lN) (by rw [o₈.get .r4, o₇.get .r4, a6 o₆ e₆,
    BitVec.add_zero]) (by rw [o₈.wr, o₇.wr, o₆.wr, h.wr]; exact sc_inW F (by unfold oRsa; omega)) fun w mw => ?_
  have k₈ : Only [.r4, .r5] t t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hK : Keep [.r4, .r5] t w := (k₈.keep.trans mw.keep).mono
  have hb : (t₈.gpr .r5).setWidth 8 = view t.mem (Sp s) lN &&& c := by
    rw [e₈, e₇, o₇.get .r18, o₆.get .r18, h.pc, L.hc, o₆.mem]
    simp only [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
    rfl
  have hm : w.mem = t.mem.writeW (off (Sp s) lN) (view t.mem (Sp s) lN &&& c) := by
    rw [mw.mem, hb, k₈.mem]
  refine wp_nil ⟨h.keep F hK (R := [⟨off (Sp s) lN, 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega))), hK, fun o ho => ?_⟩
  rw [hm, view_w8 _ _ (by unfold oRsa; omega) (by unfold oSt oRsa at *; omega)]

theorem unmask_ok {H : Hash} (hH : HashOK H) (hD : H.D = D) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs) {t : State}
    (h : Base Sp (vP D) s t) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → (∀ o < oSt, view t'.mem (Sp s) o = dbV Gs (view t.mem (Sp s)) lN dN D c o) →
      WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block clearTop) rest))) t Q := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hd1 := L.d1
  refine WP.seq (WP.mono (dbArgs_ok L hD h) fun t₄ ⟨b₄, k₄, x24, x25, x26, x27⟩ => ?_)
  subst hD
  refine WP.seq (WP.mono (mgfXor_ok F hH hGh hGl hGv (src := lN + dN) (srcLen := H.D) (dst := lN) (dstLen := dN)
    ⟨by omega, by omega, .inr (by omega), by omega⟩ b₄ x24 x25 x26 x27) fun t₅ ⟨b₅, v₅⟩ => ?_)
  have V4 : view t₄.mem (Sp s) = view t.mem (Sp s) := by rw [k₄.mem]
  rw [V4] at v₅
  refine WP.seq (WP.mono (clearTop_ok L b₅) fun w ⟨b, _, v⟩ => k w b fun o ho => ?_)
  rw [v o ho, dbV]
  by_cases e : o = lN
  · subst e; rw [ifp rfl, ifp rfl, v₅ _ ho]
  · rw [ifn e, ifn e, v₅ o ho]

end

end VG.Proof.RsaPss.PPC64LE
