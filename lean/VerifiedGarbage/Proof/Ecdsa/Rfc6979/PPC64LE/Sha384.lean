module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Kit
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Update

/-! # Deterministic ECDSA on PPC64LE: HMAC-SHA-384's functions -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- SHA-512's `update`, constant time with the pointers and lengths public. -/
theorem sha512_updCT : ConstantTime isa
    (Proof.Hmac.Stream.PPC64LE.updK 192 224 Proof.Hmac.Stream.PPC64LE.Sha384.ok.SH.Repr).pre
    (Proof.Hmac.Stream.PPC64LE.updK 192 224 Proof.Hmac.Stream.PPC64LE.Sha384.ok.SH.Repr).pub
    Impl.Sha512.PPC64LE.Stream.update :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    Proof.Sha512.PPC64LE.Stream.Update.update_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩ ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩ hp e₁ e₂

/-- HMAC-SHA-384's functions. -/
def sha384K : Kit :=
  Kit.ofStream Proof.Hmac.Stream.PPC64LE.Sha384.hash Proof.Hmac.Stream.PPC64LE.Sha384.ok Spec.Hmac.sha384I rfl
    Proof.Hmac.Stream.PPC64LE.Sha384.initScratch Proof.Hmac.Stream.PPC64LE.Sha384.finalizeScratch sha512_updCT
    (by decide) (by decide) (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
