module

public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# SLH-DSA (SHAKE) on AArch64: FORS's parameter sets

The sizes `(n, a, k)` of the six SHAKE parameter sets (`Fors.As`), for which
`forsSign`'s proofs check its blocks, and the bounds its proofs use.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG.Spec.SlhDsa

/-- `(n, a, k)` of the six SHAKE parameter sets. -/
def As (p : Params) : Prop :=
  (p.n = 16 ∧ p.a = 12 ∧ p.k = 14) ∨ (p.n = 16 ∧ p.a = 6 ∧ p.k = 33) ∨
    (p.n = 24 ∧ p.a = 14 ∧ p.k = 17) ∨ (p.n = 24 ∧ p.a = 8 ∧ p.k = 33) ∨
    (p.n = 32 ∧ p.a = 14 ∧ p.k = 22) ∨ (p.n = 32 ∧ p.a = 9 ∧ p.k = 35)

theorem As.facts {p : Params} (h : As p) :
    (p.n = 16 ∨ p.n = 24 ∨ p.n = 32) ∧ 6 ≤ p.a ∧ p.a ≤ 14 ∧ 1 ≤ p.k ∧ p.k ≤ 35 ∧
      p.k * p.a ≤ 315 ∧ p.k * 2 ^ p.a ≤ 2 ^ 32 := by
  obtain ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ := h <;>
    (rw [h₁, h₂, h₃]; decide)

end VG.Proof.SlhDsa.AArch64.Fors
