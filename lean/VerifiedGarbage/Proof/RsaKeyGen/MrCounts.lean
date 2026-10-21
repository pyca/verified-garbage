module

public import VerifiedGarbage.Proof.RsaKeyGen.MrIter

/-! # Exact blinded and uniform witness counters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Spec.RsaKeyGen

instance goSDecidable (checks : Nat) (s : Nat × Nat) : Decidable (goS checks s) :=
  inferInstanceAs (Decidable (s.1 ≤ blindedChecks ∨ s.2 < checks))

theorem mrS_first (c L : Nat) (r : Rand) : ∀ k, (mrS c L r k).1 = k + 1
  | 0 => rfl
  | k + 1 => by rw [mrS, mrS_first c L r k]

theorem mrS_uniform_le (c L : Nat) (r : Rand) : ∀ k, (mrS c L r k).2 ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have ih := mrS_uniform_le c L r k
    rw [mrS]
    split <;> omega

theorem mrS_uniform_next (c L : Nat) (r : Rand) (k : Nat) :
    (mrS c L r (k + 1)).2 = (mrS c L r k).2 + (wit c L r (L * (k + 1))).2.toNat := by
  rw [mrS]
  cases (wit c L r (L * (k + 1))).2 <;> rfl

end VG.Proof.RsaKeyGen
