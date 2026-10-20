module

import Mathlib.Data.Nat.GCD.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose the shared RSA reducer over a variable number of byte pairs.
FFDH also permits byte lengths that are not multiples of eight. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

/-- One radix-2^16 digit extends the low-digit congruence. -/
theorem trialDigit_congruence {s acc next digit value j : Nat}
    (step : next * 2 ^ 16 % s = (digit + acc) % s)
    (previous : acc * 2 ^ (16 * j) % s = value % s) :
    next * 2 ^ (16 * (j + 1)) % s = (value + 2 ^ (16 * j) * digit) % s := by
  have scale : ∀ {a b : Nat} (c : Nat), a % s = b % s → a * c % s = b * c % s :=
    fun c h => by rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have add : ∀ {a b : Nat} (c : Nat), a % s = b % s → (c + a) % s = (c + b) % s :=
    fun c h => by rw [Nat.add_mod, h, ← Nat.add_mod]
  have power : next * 2 ^ (16 * (j + 1)) = next * 2 ^ 16 * 2 ^ (16 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [power, scale _ step, Nat.add_mul, add _ previous, Nat.add_comm, Nat.mul_comm digit]

/-- Move one consumed digit from the unprocessed suffix into the scaled
accumulator, preserving the original candidate modulo the divisor. -/
theorem trialRemaining_congruence {s acc next digit remaining value j : Nat}
    (step : next * 2 ^ 16 % s = (digit + acc) % s)
    (previous : (acc + (digit + 2 ^ 16 * remaining)) * 2 ^ (16 * j) % s = value % s) :
    (next + remaining) * 2 ^ (16 * (j + 1)) % s = value % s := by
  have scale : ∀ {a b : Nat} (c : Nat), a % s = b % s → a * c % s = b * c % s :=
    fun c h => by rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have add : (next * 2 ^ 16 + remaining * 2 ^ 16) % s =
      (digit + acc + remaining * 2 ^ 16) % s := by
    rw [Nat.add_mod, step, ← Nat.add_mod]
  have power : (next + remaining) * 2 ^ (16 * (j + 1)) =
      (next * 2 ^ 16 + remaining * 2 ^ 16) * 2 ^ (16 * j) := by
    rw [← Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [power, scale _ add]
  have rearrange : digit + acc + remaining * 2 ^ 16 = acc + (digit + 2 ^ 16 * remaining) := by
    rw [Nat.mul_comm remaining]
    omega
  rw [rearrange]
  exact previous

/-- An odd divisor is coprime to every power of the reduction radix. -/
theorem trialDigit_divides {acc value divisor j : Nat}
    (odd : divisor % 2 = 1) (bound : acc < 2 * divisor)
    (congruence : acc * 2 ^ (16 * j) % divisor = value % divisor) :
    value % divisor = 0 ↔ acc = 0 ∨ acc = divisor := by
  have coprime : Nat.Coprime divisor (2 ^ (16 * j)) := by
    apply Nat.Coprime.pow_right
    show Nat.gcd divisor 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, odd]
    rfl
  rw [← congruence]
  constructor
  · intro zero
    have divides : divisor ∣ acc := coprime.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero zero)
    obtain ⟨q, eq⟩ := divides
    rcases q with _ | _ | q
    · left; rw [eq, Nat.mul_zero]
    · right; rw [eq, Nat.mul_one]
    · exfalso
      rw [eq] at bound
      have := Nat.mul_le_mul_left divisor (show 2 ≤ q + 1 + 1 by omega)
      omega
  · rintro (rfl | rfl)
    · simp
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)

end VG.Proof.Ffdh.Arm.ParameterCandidate
