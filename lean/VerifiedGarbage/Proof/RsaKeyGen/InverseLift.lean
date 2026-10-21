module

public import Mathlib.Data.Int.Basic

/-! # A one-step negative-inverse lift expressed in native-word parts -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem inverse_lift_identity {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    c * (x + b * y) + 1 = b * b * (k * k - c * q) := by
  grind

theorem inverse_lift_dvd {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    b * b ∣ c * (x + b * y) + 1 :=
  ⟨k * k - c * q, inverse_lift_identity inverse split⟩

theorem inverse_lift_nat {b c x : Nat} (inverse : (c * x + 1) % b = 0) :
    (c * (x + b * (x * ((c * x + 1) / b) % b)) + 1) % (b * b) = 0 := by
  let k := (c * x + 1) / b
  have eq₁ : c * x + 1 = b * k := by
    have := Nat.div_add_mod (c * x + 1) b
    rw [inverse, Nat.add_zero] at this
    exact this.symm
  have eq₂ : x * k = b * (x * k / b) + x * k % b := (Nat.div_add_mod (x * k) b).symm
  have I : (c : Int) * x + 1 = (b : Int) * k := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using congrArg (fun n : Nat => (n : Int)) eq₁
  have S : (x : Int) * k = (b : Int) * (x * k / b : Nat) + (x * k % b : Nat) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) eq₂
  have D : ((b * b : Nat) : Int) ∣ ((c * (x + b * (x * k % b)) + 1 : Nat) : Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using inverse_lift_dvd I S
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp D)

end VG.Proof.RsaKeyGen
