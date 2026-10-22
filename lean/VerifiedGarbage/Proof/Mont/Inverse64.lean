module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-! # Lift an existing negative inverse from one 32-bit word to two

The high word is `u * (k + c₁*u)` modulo 2^32, where
`k = (c₀*u + 1)/2^32`. This reuses the existing optimized 32-bit inverse.
-/

@[expose] public section
namespace VG.Proof.Mont

def inverseHigh (c0 c1 u : Nat) : Nat :=
  (u * ((c0 * u + 1) / 2 ^ 32 + c1 * u)) % 2 ^ 32

theorem inverse_lift {c0 c1 u : Nat} (inverse : (c0 * u + 1) % 2 ^ 32 = 0) :
    ((c0 + 2 ^ 32 * c1) * (u + 2 ^ 32 * inverseHigh c0 c1 u) + 1) % 2 ^ 64 = 0 := by
  let B := 2 ^ 32
  let k := (c0 * u + 1) / B
  let h := inverseHigh c0 c1 u
  let A := k + c1 * u
  have invB : (c0 * u + 1) % B = 0 := inverse
  have kEq : c0 * u + 1 = B * k := by
    simpa only [invB, Nat.zero_add] using (Nat.mod_add_div (c0 * u + 1) B).symm
  have highCong : Nat.ModEq B h (u * A) := Nat.mod_modEq _ _
  have innerMod : (c0 * h + A) % B = 0 := by
    calc
      _ = (c0 * (u * A) + A) % B := (highCong.mul_left c0).add_right A
      _ = ((c0 * u + 1) * A) % B := by congr 1; ring
      _ = 0 := by rw [kEq]; simp [Nat.mul_mod]
  have innerEq : c0 * h + A = B * ((c0 * h + A) / B) := by
    simpa only [innerMod, Nat.zero_add] using (Nat.mod_add_div (c0 * h + A) B).symm
  have expansion : (c0 + B * c1) * (u + B * h) + 1 =
      B ^ 2 * ((c0 * h + A) / B + c1 * h) := by
    calc
      _ = (c0 * u + 1) + B * (c0 * h + c1 * u) + B ^ 2 * (c1 * h) := by ring
      _ = B * (c0 * h + A) + B ^ 2 * (c1 * h) := by rw [kEq]; dsimp only [A]; ring
      _ = B ^ 2 * ((c0 * h + A) / B + c1 * h) := by
        conv_lhs => rw [innerEq]
        ring
  have power : B ^ 2 = 2 ^ 64 := by
    dsimp only [B]
    rw [← Nat.pow_mul]
  change ((c0 + B * c1) * (u + B * h) + 1) % 2 ^ 64 = 0
  rw [← power, expansion, Nat.mul_mod_right]

theorem inverse_carry {c0 u : Nat} (inverse : (c0 * u + 1) % 2 ^ 32 = 0) :
    (c0 * u + 1) / 2 ^ 32 = c0 * u / 2 ^ 32 + 1 := by
  have split := Nat.mod_add_div (c0 * u) (2 ^ 32)
  have small := Nat.mod_lt (c0 * u) (by decide : 0 < 2 ^ 32)
  have splitNext := Nat.mod_add_div (c0 * u + 1) (2 ^ 32)
  omega

theorem inverse_carry_bound {c0 u : Nat} (hc : c0 < 2 ^ 32) (hu : u < 2 ^ 32) :
    c0 * u / 2 ^ 32 + 1 < 2 ^ 32 := by
  have product : c0 * u ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have bound : c0 * u < 2 ^ 32 * (2 ^ 32 - 1) :=
    Nat.lt_of_le_of_lt product (by decide)
  have divBound : c0 * u / 2 ^ 32 < 2 ^ 32 - 1 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).mpr (by simpa only [Nat.mul_comm] using bound)
  omega

end VG.Proof.Mont
