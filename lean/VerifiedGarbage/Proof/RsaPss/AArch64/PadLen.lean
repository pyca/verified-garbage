import VerifiedGarbage.Proof.RsaPss.AArch64.Pad
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate

/-!
# RSASSA-PSS on AArch64: `0x80` at a public offset, and the length field

`fixedPad80` ORs `0x80` into byte `ℓ` of `Y` (`fixedPad_ok`); `lenField`
writes the length field to `scratch + oLen` with `H`'s code
(`lenField_ok`), and `lenLoop` ORs it into the end of block
`⌊(ℓ + L) / B⌋` of `Y` through a mask for each block (`lenLoop_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_orr wp_and wp_lsl
  wp_lsr wp_ldrb wp_strb wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_countdown wp_mov)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPkcs1Sig (frame_writeBytes)

/-! ## `0x80` at a public offset -/

theorem v80_fixed (V : Nat → Byte) {ℓ n : Nat} (h : ℓ < n) :
    upd V (oY + ℓ) (V (oY + ℓ) ||| 0x80) = v80 V ℓ n := by
  funext o
  simp only [upd, v80]
  by_cases e : o = oY + ℓ
  · subst e
    simp only [ite_true, show oY ≤ oY + ℓ ∧ oY + ℓ < oY + n from ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
      and_self]
  · simp only [e, ite_false]
    split
    · rw [ite_eq_right (by omega)]; simp
    · rfl

theorem or80 (b : Byte) : (BitVec.setWidth 64 b ||| (BitVec.ofNat 16 0x80).setWidth 64).setWidth 8 = b ||| 0x80 := by
  revert b; decide

theorem fixedPad_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {ℓ n : Nat} (hℓ : ℓ < n) (h4 : oY + ℓ < 4096) :
    WP isa (fixedPad80 ℓ) t fun t' => Keep [.x10, .x9, .x13] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (v80 V ℓ n) := by
  unfold fixedPad80
  refine wp_addImm h4 fun u₁ o₁ e₁ => ?_
  have hY : oY + ℓ + 1 ≤ oRsa := by unfold oY oRsa at *; omega
  refine wp_ldrb (by decide) (by rw [e₁, L.x20, BitVec.add_zero]) (by rw [o₁.rd, o₁.wr]; exact L.ld hY)
    fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_orr fun u₄ o₄ e₄ => ?_
  have O₄ : Only [.x10, .x9, .x13] t u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine wp_strb (by decide) (by rw [o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁,
      L.x20, BitVec.add_zero]) (by rw [O₄.wr]; exact L.st hY) fun u₅ m₅ => wp_nil ?_
  have hb : (u₄.gpr .x9).setWidth 8 = V (oY + ℓ) ||| 0x80 := by
    rw [e₄, o₃.get .x9, e₂, e₃, o₁.mem, R (oY + ℓ) (by omega)]
    exact or80 _
  refine ⟨(O₄.keep.trans m₅.keep).mono, ?_, ?_⟩
  · rw [m₅.mem, O₄.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := oY + ℓ) (n := 1) (by omega) (by unfold oRsa at *; omega))
  · rw [m₅.mem, O₄.mem, hb, ← v80_fixed V hℓ]
    exact R.wb (o := oY + ℓ) (by omega) _

/-! ## The length field -/

theorem lenField_ok (H : Hash) {md : Md H.P.B H.P.N H.P.L} (hs : Proof.Pbkdf2.AArch64.Shape (P := H.P) md)
    {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    (hNBL : H.P.N + H.P.B - H.P.L ≤ 192) (hL : H.P.L ≤ 16) :
    WP isa (.block (lenField H)) t fun t' => Keep [.x19, .x9, .x12] t t' ∧ t'.gpr .x19 = off S oSt ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (updL V oLen (md.lenOf (t.gpr .x22))) := by
  unfold lenField
  refine wp_addImm (by unfold oLen; omega) fun u₁ o₁ e₁ => ?_
  have ha : u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = off S oLen := by
    rw [e₁, L.x20, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; unfold oLen; omega
  have hin : InRegions u₁.wr (u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L)) H.P.L := by
    rw [ha, o₁.wr]; exact L.st (by unfold oLen oRsa; omega)
  show WP isa (.block (H.P.len ++ [.addImm .x .x19 .x20 oSt])) u₁ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (hs.len u₁ hin) (by rw [Code.allInstrs_eq]; exact hs.lenKeepsV)) fun u₂ ⟨⟨hg, hrd, hwr, hsp, hm⟩, hv⟩ => ?_
  refine wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simpa using hr.1), hg r hr.2.1 hr.2.2, o₁.gpr r (by simpa using hr.1)]
  · rw [o₃.rd, hrd, o₁.rd]
  · rw [o₃.wr, hwr, o₁.wr]
  · rw [o₃.sp, hsp, o₁.sp]
  · rw [o₃.vcs r hr, hv r hr, o₁.vcs r hr]
  · rw [e₃, hg .x20 (by decide) (by decide), o₁.get .x20, L.x20]
  · rw [o₃.mem, hm, ha, o₁.mem]
    exact (frame_writeBytes _ _ _).sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, by
        rw [md.lenOf_length]; exact Offset.sub_base _ (by unfold oLen oRsa; omega)⟩
  · rw [o₃.mem, hm, ha, o₁.mem, o₁.get .x22]
    exact R.writeBytes (by rw [md.lenOf_length]; unfold oLen oRsa; omega)

end VG.Proof.RsaPss.AArch64
