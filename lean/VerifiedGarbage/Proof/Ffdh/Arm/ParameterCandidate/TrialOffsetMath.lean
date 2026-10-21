module

import Mathlib.Data.Nat.GCD.Basic
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

theorem offset_divides_half {p divisor : Nat} (oddP : p%2=1) (oddD : divisor%2=1) :
    ((p+(divisor-1))%divisor=0) ↔ (((p-1)/2)%divisor=0) := by
  have rearrange : p+(divisor-1)=(p-1)+divisor := by omega
  rw [rearrange,Nat.add_mod_right]
  have twice : p-1=2*((p-1)/2) := by omega
  rw [twice,←Nat.dvd_iff_mod_eq_zero,←Nat.dvd_iff_mod_eq_zero]
  have coprime : Nat.Coprime 2 divisor := by
    show Nat.gcd 2 divisor=1
    rw [Nat.gcd_rec,oddD]
    rfl
  rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  exact coprime.symm.dvd_mul_left

end VG.Proof.Ffdh.Arm.ParameterCandidate
