module

public import VerifiedGarbage.Proof.Framework.PowLit

/-! # Public-exponent identities used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.Weierstrass

/-- Iterated powers, using the same core semiring powers as the code proofs. -/
theorem pow_mul_exponents {M : Type _} [Lean.Grind.Semiring M] (b : M) (n k : Nat) :
    (b ^ n) ^ k = b ^ (n * k) := by
  induction k with
  | zero => rw [Nat.mul_zero, Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero]
  | succ k ih =>
    rw [Lean.Grind.Semiring.pow_succ, ih, ← Lean.Grind.Semiring.pow_add, Nat.mul_succ]

/-- A product raised to a public exponent. -/
theorem mul_pow_exponent {M : Type _} [Lean.Grind.CommSemiring M] (a b : M) (n : Nat) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.mul_one]
  | succ n ih =>
    rw [Lean.Grind.Semiring.pow_succ, ih, Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ]
    grind

end VG.Proof.Weierstrass
