module
public import Mathlib.Data.Int.ModEq

import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Natural-number CRT recombination agrees with the signed RFC coefficient -/

@[expose] public section
namespace VG.Proof.Bignum

theorem crt_coefficient_natural {p mp mq qi : Nat} (positive : 0 < p) :
    ((((mp : Int) - mq) * qi) % (p : Int)).toNat = ((mp + p - mq % p) % p * qi) % p := by
  apply crt_h (R := 1) (a := mp) (b := mq % p) positive (by simp)
  · simp only [Nat.mul_one]
  · simp only [Nat.mul_one, Nat.mod_mod]
  · exact Nat.mod_lt _ positive
  · simp only [Nat.mul_one, Nat.mod_mod]
  · exact Nat.mod_lt _ positive

theorem crt_recombine_bound {p q mp mq qi : Nat} (hp : 0 < p) (mqBound : mq < q) :
    mq + q * (((mp + p - mq % p) % p * qi) % p) < p * q := by
  have h := Nat.mod_lt ((mp + p - mq % p) % p * qi) hp
  have H := Nat.mul_le_mul_left q h
  rw [Nat.mul_succ, Nat.mul_comm q p] at H
  omega

end VG.Proof.Bignum
