module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre

/-!
# RSASSA-PSS verification on PPC64LE: the hash calls

Untrusted: everything here is checked by Lean. `hInit_ok`, `hUpd_ok` and
`hFin_ok`: `hInit`, `hUpd` and `hFin`, the calls of the streaming functions
on the state at `S + oSt` (by `init_ok`, `upd_ok` and `fin_ok`, shared with
RSAES-OAEP encryption), `update`'s data in our part of the working space
after the ranges the calls write (`oY` on).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR sc_inW sc_cov sdis cR_dis fx hiRegs
  Same init_ok upd_ok fin_ok hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_addi wp_nil)

theorem pres_of {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

section
variable {D : Nat} {s : State} (F : Fits Sp s) {H : Hash} (hH : HashOK H)
include F hH

theorem hInit_ok {t : State} (h : Base Sp (vP D) s t) :
    WP isa (hInit H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (Sp s) oSt) [] := by
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_nil ?_)
  refine WP.mono (init_ok F hH (h.only F o₁) (by rw [e₁, h.r14])) fun t' ⟨b, g, sm, r⟩ =>
    ⟨b, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr], (Same.of_mem o₁.mem _).trans sm, r⟩

theorem hUpd_ok {t : State} (h : Base Sp (vP D) s t) {m : List Byte} (hr : hH.SH.Repr t.mem (off (Sp s) oSt) m)
    (h4 : t.gpr .r4 = BitVec.ofNat 64 m.length) {d len : Nat} (h5 : t.gpr .r5 = off (Sp s) d)
    (h6 : t.gpr .r6 = BitVec.ofNat 64 len) (hd : oY ≤ d) (hl : d + len ≤ oRsa) :
    WP isa (hUpd H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' [(oSt, H.S), (oW, H.W)] ∧
      hH.SH.Repr t'.mem (off (Sp s) oSt) (m ++ Spec.Sha256.bytesAt t.mem (off (Sp s) d) len) := by
  have Fh := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hY : oY = 2560 := rfl
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_nil ?_)
  have k₂ : Only [.r3, .r7] t t₂ := (o₁.trans o₂).mono
  have b₂ := h.only F k₂
  refine WP.mono (upd_ok F hH b₂ (dat := off (Sp s) d) (len := len) (by rw [o₂.get .r3, e₁, h.r14])
    (by rw [k₂.get .r5, h5]) (by rw [k₂.get .r6, h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold oRsa at hl; omega)])
    (by rw [e₂, o₁.get .r14, h.r14]) (Covers.right (by rw [b₂.wr]; exact sc_cov F hl))
    (sdis (.inr (by omega)) hl (by omega)) (sdis (.inr (by omega)) hl (by omega)) (cR_dis F hl))
    fun t' ⟨b, g, sm, r⟩ => ⟨b, fun r hr => by rw [g r hr, pres_of k₂ (by decide) r hr], (Same.of_mem k₂.mem _).trans sm,
      ?_⟩
  have := r m (by rw [k₂.mem]; exact hr) (by rw [k₂.get .r4, h4])
  rwa [k₂.mem] at this

theorem hFin_ok {t : State} (h : Base Sp (vP D) s t) {m : List Byte} (hr : hH.SH.Repr t.mem (off (Sp s) oSt) m)
    (h4 : t.gpr .r4 = BitVec.ofNat 64 m.length) (hm : m.length < 2 ^ 64) :
    WP isa (hFin H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Sha256.bytesAt t'.mem (off (Sp s) oDig) H.FD = hH.fh m := by
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r3, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have b₃ := h.only F k₃
  refine WP.mono (fin_ok F hH b₃ (by rw [o₃.get .r3, o₂.get .r3, e₁, h.r14]) (by rw [o₃.get .r5, e₂, o₁.get .r14,
    h.r14]) (by rw [e₃, o₂.get .r14, o₁.get .r14, h.r14])) fun t' ⟨b, g, sm, r⟩ =>
    ⟨b, fun r hr => by rw [g r hr, pres_of k₃ (by decide) r hr], (Same.of_mem k₃.mem _).trans sm,
      r m (by rw [k₃.mem]; exact hr) hm (by rw [k₃.get .r4, h4])⟩

end

end VG.Proof.RsaPss.PPC64LE
