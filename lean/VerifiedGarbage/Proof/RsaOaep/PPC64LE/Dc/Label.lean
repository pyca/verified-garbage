module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Label
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSAES-OAEP decryption on PPC64LE: the label's hash

Untrusted: everything here is checked by Lean. In the decoding, whose
`Base` is relative to the entry state with memory `m` (`withMem s m`),
`hashLabel_ok`: `init`, `update` with the label (`r18`, `r19`) and
`finalize` write `H(label)`, as `finalize` writes it, to `scratch + oDig`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

theorem fitsM : Fits (SD s) (withMem s m) := fits P rfl rfl

/-- A buffer the decoding only reads, apart from the stack and `scratch`: as
in `m`. -/
theorem bytes_m {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) {R : Region} (hk : (kD s).Disjoint R)
    (hs : (scR s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m R.base R.len :=
  bytes_entry h.mem (hk.sub_left kR_sub) (hs.sub_left (sc_sub P)) hl

theorem hashLabel_ok {H : Hash} (hH : HashOK H) {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (Dec.hashLabel H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧ Same (Sd s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Rsa.bytesAt t'.mem (off (Sd s) oDig) H.FD =
        hH.fh (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
  have F := hfits hH
  have PF := fitsM (m := m) P
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_nil ?_)
  have b₁ := h.only PF o₁
  refine WP.seq (WP.mono (init_ok PF hH b₁ (by rw [e₁, h.r14])) fun t₂ ⟨b₂, g₂, s₂, r₂⟩ => ?_)
  refine WP.seq (wp_addi fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ =>
    wp_mov fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r3, .r4, .r5, .r6, .r7] t₂ t₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have b₇ := b₂.only PF k₇
  have hl : lR s ∈ (withMem s m).rd := by show lR s ∈ s.rd; rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (stackArg s 9) (stackArg s 10).toNat =
      Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat :=
    bytes_m P b₇ (R := lR s) P.kl P.ls.symm (by show (stackArg s 10).toNat ≤ _; have := (stackArg s 10).isLt; omega)
  refine WP.seq (WP.mono (upd_ok PF hH b₇ (dat := stackArg s 9) (len := (stackArg s 10).toNat)
    (by rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, b₂.r14])
    (by rw [o₇.get .r5, o₆.get .r5, e₅, o₄.get .r18, o₃.get .r18, Base.r18 b₂])
    (by rw [o₇.get .r6, e₆, o₅.get .r19, o₄.get .r19, o₃.get .r19, Base.r19 b₂])
    (by rw [e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, b₂.r14])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)))
    (P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha))) fun t₈ ⟨b₈, g₈, s₈, r₈⟩ => ?_)
  refine WP.seq (wp_addi fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ => wp_addi fun t₁₁ o₁₁ e₁₁ =>
    wp_addi fun t₁₂ o₁₂ e₁₂ => wp_nil ?_)
  have k₁₂ : Only [.r3, .r4, .r5, .r6] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only PF k₁₂
  have g4 : t₁₂.gpr .r4 = stackArg s 10 := by
    rw [o₁₂.get .r4, o₁₁.get .r4, e₁₀, o₉.get .r19, Base.r19 b₈]
  have hr : hH.SH.Repr t₁₂.mem (off (Sd s) oSt) (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (fin_ok PF hH b₁₂ (by rw [o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, e₉, b₈.r14])
    (by rw [o₁₂.get .r5, e₁₁, o₁₀.get .r14, o₉.get .r14, b₈.r14]) (by rw [e₁₂, o₁₁.get .r14, o₁₀.get .r14,
      o₉.get .r14, b₈.r14])) fun t' ⟨b', g', s', r'⟩ => ⟨b', fun r hr' => ?_, ?_, ?_⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (Sd s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (stackArg s 10).isLt; omega)
      (by rw [g4, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

end

end VG.Proof.RsaOaep.PPC64LE.Dec
