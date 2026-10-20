module
public import Mathlib.Data.Int.ModEq

import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # The natural residue difference is the RSA specification's signed difference -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

theorem crt_coefficient_value {P a b qi : Nat} (positive : 0 < P) :
    ((a + P - b % P) % P * qi) % P = ((((a : Int) - b) * qi) % (P : Int)).toNat := by
  symm
  apply VG.Proof.Bignum.crt_h (R := 1) (a := a) (b := b % P) positive (Nat.coprime_one_left P)
    (by simp only [Nat.mul_one]) (by simp only [Nat.mul_one, Nat.mod_mod]) (Nat.mod_lt _ positive)
    (by simp only [Nat.mul_one, Nat.mod_mod]) (Nat.mod_lt _ positive)

end VG.Proof.Bignum.Arm
