module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em

/-!
# RSAES-OAEP encryption on PPC64LE: the label's hash

Untrusted: everything here is checked by Lean. `hashLabel_ok`: `hashLabel`
writes what the streaming `finalize` of `H` writes for the label to
`S + oDig`; `copyLh_ok`: `copyLh` copies its first `hLen` bytes, `lHash`,
to `EM + 1 + hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- An `Only` step keeps the callee-saved registers it does not write. -/
theorem only_pres {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `hashLabel`: what `finalize` writes for the label, to `S + oDig`. -/
theorem hashLabel_ok {H : Hash} (hH : HashOK H) {t : State} (h : Base S vO s t) :
    WP isa (hashLabel H) t fun t' => Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Rsa.bytesAt t'.mem (off (S s) oDig) H.FD =
        hH.fh (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_nil ?_)
  have b₁ := h.only P.fits o₁
  refine WP.seq (WP.mono (init_ok P.fits hH b₁ (by rw [e₁, h.r14])) fun t₂ ⟨b₂, g₂, s₂, r₂⟩ => ?_)
  refine WP.seq (wp_addi fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ =>
    wp_mov fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r3, .r4, .r5, .r6, .r7] t₂ t₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have b₇ := b₂.only P.fits k₇
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (s.gpr .r9) (s.gpr .r10).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat :=
    bytes_entry b₇.mem P.kl ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega_arith)
  refine WP.seq (WP.mono (upd_ok P.fits hH b₇ (dat := s.gpr .r9) (len := (s.gpr .r10).toNat)
    (by rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, b₂.r14])
    (by rw [o₇.get .r5, o₆.get .r5, e₅, o₄.get .r19, o₃.get .r19, b₂.r19])
    (by rw [o₇.get .r6, e₆, o₅.get .r20, o₄.get .r20, o₃.get .r20, b₂.r20])
    (by rw [e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, b₂.r14])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    (P.kl.sub_left (cR_sub s))) fun t₈ ⟨b₈, g₈, s₈, r₈⟩ => ?_)
  refine WP.seq (wp_addi fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ => wp_addi fun t₁₁ o₁₁ e₁₁ =>
    wp_addi fun t₁₂ o₁₂ e₁₂ => wp_nil ?_)
  have k₁₂ : Only [.r3, .r4, .r5, .r6] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only P.fits k₁₂
  have g4 : t₁₂.gpr .r4 = s.gpr .r10 := by
    rw [o₁₂.get .r4, o₁₁.get .r4, e₁₀, o₉.get .r20, b₈.r20]
  have hr : hH.SH.Repr t₁₂.mem (off (S s) oSt) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (fin_ok P.fits hH b₁₂ (by rw [o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, e₉, b₈.r14])
    (by rw [o₁₂.get .r5, e₁₁, o₁₀.get .r14, o₉.get .r14, b₈.r14]) (by rw [e₁₂, o₁₁.get .r14, o₁₀.get .r14,
      o₉.get .r14, b₈.r14])) fun t' ⟨b', g', s', r'⟩ => ⟨b', fun r hr' => ?_, ?_, ?_⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (S s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (s.gpr .r10).isLt; omega_arith)
      (by rw [g4, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `copyLh`: the first `hLen` bytes at `S + oDig` to `EM + 1 + hLen`. -/
theorem copyLh_ok {H : Hash} (hH : HashOK H) (hD : H.D = D) {t : State} (h : Base S vO s t) :
    WP isa (copyLh H) t fun t' => Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (S s) (1 + D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) D) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  subst hD
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_addi (h := by unfold oEm; omega_arith) fun t₂ o₂ e₂ =>
    wp_li (by omega_arith) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copy_ok (q := off (S s) oDig) (p := off (S s) (1 + H.D)) (n := H.D) hD0 (by omega_arith)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14]; show off (S s) (oEm + 1 + H.D) = _; congr 2)
    (by rw [e₃]) (fun j hj => by
      rw [k₃.rd, k₃.wr, h.wr]
      show InRegions _ (off (off (S s) oDig) j) 1
      rw [off_off]; exact sc_inR P.fits (by omega_arith) _)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1 + H.D) (by omega_arith))
    (fun j hj i hi => by
      show off (off (S s) oDig) j ≠ off (off (S s) (1 + H.D)) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) (1 + H.D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) H.D) := by
    rw [hm, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; omega_arith) hm', fun r hr => hK.gpr r (by revert r; decide), hm'⟩

end

/-- `EM` before masking, from its part before `lHash` and `lHash` written
after it. -/
theorem emAt_of {V V' : Nat → Byte} {k D mLen : Nat} {sd lh m : List Byte} (hp : EmPart V k D sd m mLen)
    (hk : 2 * D + 2 + mLen ≤ k) (hk2 : k ≤ 1024)
    (hV : ∀ o < 1024, V' o = if 1 + D ≤ o ∧ o < 1 + D + D then lh.getD (o - (1 + D)) 0 else V o) :
    RsaOaep.EmAt V' k D sd lh m mLen where
  z0 := by rw [hV 0 (by omega_arith), ifn (by omega_arith)]; exact hp.z0
  sd i hi := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.sd i hi
  lh i hi := by rw [hV _ (by omega_arith), ifp (by omega_arith), Nat.add_sub_cancel_left]
  ps i h₁ h₂ := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.ps i (by omega_arith) h₂
  one := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.one
  msg i hi := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.msg i hi


end VG.Proof.RsaOaep.PPC64LE
