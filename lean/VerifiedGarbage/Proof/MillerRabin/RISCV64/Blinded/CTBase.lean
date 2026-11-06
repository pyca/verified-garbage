module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time, two runs' predicates

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/CTBase.lean`): two runs of
the loop are related as RSA's signature verification relates them
(`Proof/RsaPkcs1Sig/RISCV64/Two.lean`): both satisfy the same predicate for
the same public data, whatever else memory holds. A predicate implied by one
with pins has them (`Pins.of_imp`), and two runs can be related through a map
of their public data (`two_map`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A predicate implied by one with pins has them. -/
theorem Pins.of_imp {α : Type} {Φ Ψ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs)
    (hi : ∀ a s, Ψ a s → Φ a s) : Pins Ψ rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ (hi a s₁ h₁) (hi a s₂ h₂)

/-- Two runs related through a map of their public data. -/
theorem two_map {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop} (f : α → β)
    (hf : ∀ a s, Φ a s → Ψ (f a) s) {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two Ψ) c Q) : RelCT isa (Two Φ) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨f a, hf a _ h₁, hf a _ h₂⟩) fun _ _ h => h

end VG.Proof.MillerRabin.RISCV64.Blinded
