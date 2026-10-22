module

public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee

/-!
# SM4-GCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs relate
two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as AES-GCM's
(`Proof/AesGcm/AArch64/RelBase.lean`), each call by its callee's proof
(`rel_ctr`, `rel_key`, and AES-GCM's `rel_gh`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT GhashImpl GhCall gh_rel)

theorem rel_gh (g : GhashImpl) {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call g.fn.name g.fn.code) TT :=
  gh_rel g fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr {σ₁ σ₂ : State} {K C D : Addr} {n : Nat} (h₁ : CtrCall σ₁ K C D n)
    (h₂ : CtrCall σ₂ K C D n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) ctrCall TT :=
  ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K C : Addr} (h₁ : KeyCall σ₁ K C) (h₂ : KeyCall σ₂ K C)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call "vg_sm4_expand_key" keyCode) TT :=
  key_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, h₁, h₂, hsp⟩

end VG.Proof.Sm4Gcm.AArch64
