module

public import VerifiedGarbage.Proof.Rsa.RecoverExp

/-! # Subtraction in the recovery algorithm's fixed-width arrays -/

@[expose] public section
namespace VG.Proof.Rsa

def sub32 (w a b : Nat) : Nat := (a + 2 ^ (32 * w) - b) % 2 ^ (32 * w)

theorem sub32_of {X a b w c : Nat} (hX : X < 2 ^ (32 * w)) (hb : b < 2 ^ (32 * w))
    (h : X + b = a + 2 ^ (32 * w) * c) (hc : c ≤ 1) : X = sub32 w a b ∧ c = b2n (decide (a < b)) := by
  unfold sub32
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · refine ⟨?_, by simp [b2n]; omega⟩
    rw [Nat.mul_zero, Nat.add_zero] at h
    rw [show a + 2 ^ (32 * w) - b = X + 2 ^ (32 * w) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hX]
  · refine ⟨?_, by simp [b2n]; omega⟩
    rw [Nat.mul_one] at h
    rw [show a + 2 ^ (32 * w) - b = X by omega, Nat.mod_eq_of_lt hX]

theorem sub32_one {w y : Nat} (h1 : 1 ≤ y) (h2 : y < 2 ^ (32 * w)) : sub32 w y 1 = y - 1 := by
  unfold sub32
  rw [show y + 2 ^ (32 * w) - 1 = (y - 1) + 2 ^ (32 * w) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Rsa
