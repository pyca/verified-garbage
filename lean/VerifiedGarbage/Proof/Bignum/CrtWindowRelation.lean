module
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Integer relations for a complete window on arbitrary reduced table entries. -/

@[expose] public section
namespace VG.Proof.Bignum.CrtWindowFive

theorem square_scale {m y y' a R k : Nat}
    (hs : y' * R % m = y * y % m) (hy : y * R ^ k % m = a % m) :
    y' * R ^ (2 * k + 1) % m = a ^ 2 % m := by
  have h₁ := congrArg (fun z => z * (R ^ k * R ^ k) % m) hs
  have h₂ := congrArg (fun z => z * z % m) hy
  simp only [Nat.mod_mul_mod, Nat.mul_mod_mod] at h₁ h₂
  have e₁ : y' * R ^ (2 * k + 1) = (y' * R) * (R ^ k * R ^ k) := by
    rw [show 2 * k + 1 = k + k + 1 by omega, Nat.pow_add, Nat.pow_add, Nat.pow_one]
    ac_rfl
  have e₂ : y * y * (R ^ k * R ^ k) = (y * R ^ k) * (y * R ^ k) := by ac_rfl
  rw [e₁,h₁,e₂,h₂,Nat.pow_two]

theorem product_scale {m y y' a t R k : Nat}
    (hp : y' * R % m = y * t % m) (hy : y * R ^ k % m = a % m) :
    y' * R ^ (k + 1) % m = a * t % m := by
  have h₁ := congrArg (fun z => z * R ^ k % m) hp
  have h₂ := congrArg (fun z => z * t % m) hy
  simp only [Nat.mod_mul_mod] at h₁ h₂
  have e₁ : y' * R ^ (k + 1) = (y' * R) * R ^ k := by
    rw [Nat.pow_succ]
    ac_rfl
  have e₂ : y * t * R ^ k = (y * R ^ k) * t := by ac_rfl
  rw [e₁,h₁,e₂,h₂]

end VG.Proof.Bignum.CrtWindowFive
