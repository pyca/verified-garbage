module

import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega


/-! # A low-part nonzero bit reduces comparison with a power of two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem le_power_iff {low high power : Nat} (positive : 0 < power) (bound : low < power) :
    low + power * high ≤ power ↔ high + (decide (low ≠ 0)).toNat ≤ 1 := by
  by_cases zero : low = 0
  · rw [zero, decide_eq_false (by omega_using [] : ¬ (0 : Nat) ≠ 0)]
    change 0 + power * high ≤ power ↔ high + 0 ≤ 1
    constructor
    · intro H
      refine Classical.byContradiction fun bad => ?_
      have := Nat.mul_le_mul_left power (by omega_using [bad] : 2 ≤ high)
      omega_using [positive, H, this]
    · intro H
      have := Nat.mul_le_mul_left power (show high ≤ 1 by omega_using [H])
      omega_using [this]
  · rw [decide_eq_true zero]
    change low + power * high ≤ power ↔ high + 1 ≤ 1
    constructor
    · intro H
      refine Classical.byContradiction fun bad => ?_
      have := Nat.mul_le_mul_left power (by omega_using [bad] : 1 ≤ high)
      omega_using [zero, H, this]
    · intro H
      have : high = 0 := by omega_using [H]
      rw [this, Nat.mul_zero]
      omega_using [bound]

theorem le_power_nibble {low nibble high power : Nat} (positive : 0 < power) (bound : low < power) :
    low + power * (nibble + 16 * high) ≤ power ↔
      high = 0 ∧ nibble + (decide (low ≠ 0)).toNat ≤ 1 := by
  rw [le_power_iff positive bound]
  omega_using []

theorem le_native_threshold {low word high radix : Nat} (positive : 0 < radix) (bound : low < radix) :
    low + radix * (word + 2 ^ 32 * high) ≤ radix * 2 ^ 28 ↔
      high = 0 ∧ word / 2 ^ 28 + (decide (low ≠ 0 ∨ word % 2 ^ 28 ≠ 0)).toNat ≤ 1 := by
  let bottom := low + radix * (word % 2 ^ 28)
  have split := Nat.div_add_mod word (2 ^ 28)
  have remainder := Nat.mod_lt word (by decide : 0 < 2 ^ 28)
  have endBound := Nat.mul_le_mul_left radix (by omega_using [] : word % 2 ^ 28 + 1 ≤ 2 ^ 28)
  rw [Nat.mul_add, Nat.mul_one] at endBound
  have bottomBound : bottom < radix * 2 ^ 28 := by dsimp only [bottom]; omega_using [bound, endBound]
  have rearrange : low + radix * (word + 2 ^ 32 * high) =
      bottom + (radix * 2 ^ 28) * (word / 2 ^ 28 + 16 * high) := by
    dsimp only [bottom]
    rw [show (2 : Nat) ^ 32 = 2 ^ 28 * 16 by decide]
    grind
  have zero : bottom = 0 ↔ low = 0 ∧ word % 2 ^ 28 = 0 := by
    dsimp only [bottom]
    rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero]
    have nz : radix ≠ 0 := Nat.ne_of_gt positive
    simp only [nz, false_or]
  rw [rearrange, le_power_nibble (Nat.mul_pos positive (by decide)) bottomBound]
  have nonzero : decide (bottom ≠ 0) = decide (low ≠ 0 ∨ word % 2 ^ 28 ≠ 0) := by
    apply decide_eq_decide.mpr
    omega_using [zero]
  rw [nonzero]

end VG.Proof.RsaKeyGen
