module
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # The final DSA p-candidate reduction

The existing native quotient/remainder routine can reduce by the even
modulus `2*q`. Subtracting its remainder and adding one gives a candidate
whose predecessor is divisible by q. No primality assumption is needed.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation

/-- Exact quotient form of A.1.1.2 step 11. -/
theorem pReduction_quotient (x q : Nat) :
    x + 1 - x % (2 * q) = 2 * q * (x / (2 * q)) + 1 := by
  have h := Nat.mod_add_div x (2 * q)
  omega

/-- Division's remainder is safe to subtract, even before the bit-size check. -/
theorem pReduction_sub (x q : Nat) :
    x + 1 - x % (2 * q) = (x - x % (2 * q)) + 1 := by
  have := Nat.mod_le x (2 * q)
  omega

/-- Every reduced candidate is odd. -/
theorem pReduction_odd (x q : Nat) : (x + 1 - x % (2 * q)) % 2 = 1 := by
  rw [pReduction_quotient]
  simp [Nat.add_mod, Nat.mul_assoc]

/-- The quotient used by generator construction is exactly twice the
quotient from candidate reduction. -/
theorem pReduction_generatorExponent (x : Nat) {q : Nat} (hq : 0 < q) :
    (x + 1 - x % (2 * q) - 1) / q = 2 * (x / (2 * q)) := by
  rw [pReduction_quotient, Nat.add_sub_cancel]
  rw [Nat.mul_comm 2 q, Nat.mul_assoc, Nat.mul_div_right _ hq]

/-- The structural divisibility check holds for every reduced candidate. -/
theorem pReduction_divides (x q : Nat) : (x + 1 - x % (2 * q) - 1) % q = 0 := by
  rw [pReduction_quotient, Nat.add_sub_cancel]
  simp [Nat.mul_mod]

/-- Shaping may set the low bit before division: an even divisor makes
that bit irrelevant to the quotient and therefore to the p candidate. -/
theorem pReduction_orOne (x q : Nat) :
    (x ||| 1) + 1 - (x ||| 1) % (2 * q) = x + 1 - x % (2 * q) := by
  rw [pReduction_quotient, pReduction_quotient]
  have hd : (x ||| 1) / 2 = x / 2 := by rw [Nat.or_div_two]; simp
  rw [← Nat.div_div_eq_div_mul, hd, Nat.div_div_eq_div_mul]

end VG.Proof.Dsa.Generation
