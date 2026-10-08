import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-!
# AES-GCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs relate
two runs from given states (`Eq2 σ₁ σ₂`) piece by piece (`RelBase.lean`),
each call by its callee's proof (`rel_gh`, `rel_ctr`, `rel_key`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem rel_gh (g : GhashImpl) {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call g.fn.name g.fn.code) TT :=
  gh_rel g fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr (v : Ctr32Impl) {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.call v.callee.name v.callee.code) TT :=
  ctr_rel v fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key (k : KeyImpl) {σ₁ σ₂ : State} {K C S : Addr} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call k.fn.name k.fn.code) TT :=
  key_rel k fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, S, L, h₁, h₂, hsp⟩

end VG.Proof.AesGcm.AArch64
