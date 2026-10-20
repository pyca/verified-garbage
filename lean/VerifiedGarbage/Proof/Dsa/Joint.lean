module

import VerifiedGarbage.Proof.Framework.PowLit

/-! # Arithmetic identities for joint fixed-window exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa

/-- The table index has one base-four digit from each exponent. -/
theorem joint_index {i j : Nat} (hi : i < 4) (hj : j < 4) :
    4 * i + j < 16 ∧ (4 * i + j) / 4 = i ∧ (4 * i + j) % 4 = j := by
  omega

/-- Four joint windows consume exactly one byte from each exponent. -/
theorem joint_byte_step {v z j : Nat} (hv : v < 256) (hz : z < 256) (hj : j < 4)
    (E F : Nat) :
    4 * (E * 4 ^ j + v / 4 ^ (4 - j)) + ((256 * v + z) * 4 ^ j) / 16384 % 4 =
      E * 4 ^ (j + 1) + v / 4 ^ (4 - (j + 1)) ∧
    4 * (F * 4 ^ j + z / 4 ^ (4 - j)) + ((256 * v + z) * 4 ^ j) / 64 % 4 =
      F * 4 ^ (j + 1) + z / 4 ^ (4 - (j + 1)) := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.mul_one, Nat.div_one] <;> omega

end VG.Proof.Dsa
