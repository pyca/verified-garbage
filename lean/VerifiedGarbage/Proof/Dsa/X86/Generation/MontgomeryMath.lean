module

public import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Residues for the short Montgomery setup schedule. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation

theorem montgomery_seed_power {n bits : Nat} (bound : bits ≤ 64 * n) :
    2 ^ (65 * n - (bits - 1)) * 2 ^ (bits - 1) = 2 ^ n * 2 ^ (64 * n) := by
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

theorem montgomery_square_residue {n m : Nat} {v : Nat → Nat}
    (coprime : Nat.Coprime (2 ^ (64 * n)) m)
    (seed : v 0 % m = 2 ^ n * 2 ^ (64 * n) % m)
    (steps : ∀ i < 6, v (i + 1) * 2 ^ (64 * n) % m = v i * v i % m) :
    v 6 % m = 2 ^ (64 * n) * 2 ^ (64 * n) % m := by
  have loop : ∀ i ≤ 6, v i % m = 2 ^ (2 ^ i * n) * 2 ^ (64 * n) % m := by
    intro i hi
    induction i with
    | zero => simpa only [Nat.pow_zero, Nat.one_mul] using seed
    | succ i ih =>
      have h := VG.Proof.Bignum.mont_sq coprime (ih (by omega)) (steps i (by omega))
      rw [show 2 * (2 ^ i * n) = 2 ^ (i + 1) * n by
        rw [Nat.pow_succ]; ac_rfl] at h
      exact h
  exact loop 6 (by decide)

end VG.Proof.Dsa.X86.Generation
