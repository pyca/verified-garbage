import VerifiedGarbage.Proof.Bignum.Words

/-!
# RSA with the CRT: the mask of the private key's checks

`keyMask`: the mask of `c < n`, `p q = n` and `qInv < p`, which the checks
and into `sMask` one at a time (`mask_and`); a factor of the odd `n` is odd
(`odd_of_mul_odd`).
-/

namespace VG.Proof.Bignum

theorem mask_and (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

theorem odd_of_mul_odd {P Q N : Nat} (h : P * Q = N) (hN : N % 2 = 1) : P % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one P with hP | hP
  · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
  · exact hP

/-- The mask of the private key's checks. -/
def keyMask (m0 : Bool) (N P Q QI : Nat) : Bool := m0 && decide (P * Q = N) && decide (QI < P)

end VG.Proof.Bignum
