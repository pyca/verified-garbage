module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Words

/-! # A saturating upper word preserves every public-exponent validity check -/

@[expose] public section

namespace VG.Proof.Bignum
open VG

def exponentHigh (x : Nat) : Nat := min 2 (x / 2 ^ 32)

theorem exponentHigh_step (x b : Nat) (hb : b < 256) :
    min 2 (256 * exponentHigh x + x % 2 ^ 32 / 2 ^ 24) = exponentHigh (256 * x + b) := by
  have low := Nat.mod_lt x (by decide : 0 < 2 ^ 32)
  have rem := Nat.mod_lt (x % 2 ^ 32) (by decide : 0 < 2 ^ 24)
  have splitX := Nat.div_add_mod x (2 ^ 32)
  have splitLow := Nat.div_add_mod (x % 2 ^ 32) (2 ^ 24)
  unfold exponentHigh
  omega

theorem exponentLow_step (x b : Nat) :
    (256 * (x % 2 ^ 32) + b) % 2 ^ 32 = (256 * x + b) % 2 ^ 32 := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem exponentHigh_bound (x : Nat) : exponentHigh x ≤ 2 := Nat.min_le_left _ _

theorem exponent_valid_words (x : Nat) :
    Spec.Rsa.exponentValid x =
      (decide (exponentHigh x < 2) && decide (0 < exponentHigh x ∨ 3 ≤ x % 2 ^ 32) &&
        decide (x % 2 ^ 32 % 2 = 1)) := by
  have splitX := Nat.div_add_mod x (2 ^ 32)
  have low := Nat.mod_lt x (by decide : 0 < 2 ^ 32)
  have parity : x % 2 ^ 32 % 2 = x % 2 := Nat.mod_mod_of_dvd x (by decide)
  have upper : exponentHigh x < 2 ↔ x < 2 ^ 33 := by unfold exponentHigh; omega
  have lower : (0 < exponentHigh x ∨ 3 ≤ x % 2 ^ 32) ↔ 3 ≤ x := by unfold exponentHigh; omega
  simp only [Spec.Rsa.exponentValid, upper, lower, parity, Bool.beq_eq_decide_eq]
  cases decide (x % 2 = 1) <;> cases decide (3 ≤ x) <;> cases decide (x < 2 ^ 33) <;> rfl

end VG.Proof.Bignum
