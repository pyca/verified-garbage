module

import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa

/-! Canonical Montgomery products add arbitrary fixed-base exponents. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Proof.Bignum
open VG.Spec.Rsa (powMod)

theorem mont_product_encoded {g E F R M a b c : Nat}
    (coprime : Nat.Coprime R M) (canonical : c < M)
    (left : a = powMod g E M * R % M) (right : b = powMod g F M * R % M)
    (product : c * R % M = a * b % M) :
    c = powMod g (E+F) M * R % M := by
  apply Eq.trans (Nat.mod_eq_of_lt canonical).symm
  apply mont_cancel coprime
  rw [product,left,right,powMod_eq,powMod_eq,powMod_eq]
  simp only [Nat.mod_mul_mod,Nat.mul_mod_mod]
  rw [Nat.mul_assoc (g^(E+F)%M) R R, Nat.mod_mul_mod]
  congr 1
  rw [Nat.pow_add]
  ring

theorem mont_square_encoded {g E R M a c : Nat}
    (coprime : Nat.Coprime R M) (canonical : c < M)
    (encoded : a = powMod g E M * R % M)
    (square : c * R % M = a * a % M) :
    c = powMod g (2*E) M * R % M := by
  simpa only [show E+E=2*E by omega] using mont_product_encoded coprime canonical encoded encoded square

end VG.Proof.Rsa.FixedBaseComb
