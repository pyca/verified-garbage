module
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Arithmetic for extracting eight five-bit windows from a group of five
big-endian exponent bytes. No padding bits are added to the exponent. -/

@[expose] public section

namespace VG.Proof.Bignum.CrtWindowFive

/-- Appending the next base-32 digit advances the consumed prefix. -/
theorem prefix_step (v k : Nat) :
    32 * (v / 32 ^ (k + 1)) + v / 32 ^ k % 32 = v / 32 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- Each selection index is in the 32-entry table. -/
theorem digit_lt (v k : Nat) : v / 32 ^ k % 32 < 32 := Nat.mod_lt _ (by decide)

/-- The exponent invariant after the next window in a five-byte group. -/
theorem group_step (E v j : Nat) (hj : j < 8) :
    32 * (E * 32 ^ j + v / 32 ^ (8 - j)) + v / 32 ^ (7 - j) % 32 =
      E * 32 ^ (j + 1) + v / 32 ^ (7 - j) := by
  have h := prefix_step v (7 - j)
  rw [show 7 - j + 1 = 8 - j by omega] at h
  rw [Nat.pow_succ]
  grind

/-- A complete five-byte group contributes exactly its 40 bits. -/
theorem group_end (E v : Nat) : E * 32 ^ 8 + v / 32 ^ 0 = E * 256 ^ 5 + v := by
  simp only [Nat.pow_zero, Nat.div_one]

/-- A tail bit extends the pending digit, without changing the exponent
already represented by completed windows. -/
theorem pending_step (E v b bit : Nat) :
    2 * (E * 2 ^ b + v) + bit = E * 2 ^ (b + 1) + (2 * v + bit) := by
  rw [Nat.pow_succ]
  grind

theorem pending_bound {v b bit : Nat} (hv : v < 2 ^ b) (hb : bit < 2) :
    2 * v + bit < 2 ^ (b + 1) := by
  rw [Nat.pow_succ]
  omega

/-- On collecting the fifth bit, consume exactly the pending digit. -/
theorem pending_full (E v bit : Nat) :
    2 * (E * 2 ^ 4 + v) + bit = 32 * E + (2 * v + bit) := by
  omega

/-- A partial final window selects a valid table entry without appending
zero bits to the exponent. -/
theorem pending_index {v b : Nat} (hv : v < 2 ^ b) (hb : b < 5) : v < 32 := by
  have hpow : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Reconstruct the low `n + 1` base-32 digits after consuming the high one. -/
theorem group_reconstruct (E V n : Nat) :
    (32 * E + V / 2 ^ (5 * n) % 32) * 32 ^ n + V % 32 ^ n =
      E * 32 ^ (n + 1) + V % 32 ^ (n + 1) := by
  have hp : 2 ^ (5 * n) = 32 ^ n := by rw [Nat.pow_mul]
  rw [hp, Nat.mod_pow_succ, Nat.pow_succ]
  grind

end VG.Proof.Bignum.CrtWindowFive
