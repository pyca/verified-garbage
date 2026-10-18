module

public import VerifiedGarbage.Proof.Framework.Omega

/-! # Exact multiplication through a sufficiently large power-of-two modulus -/

@[expose] public section
namespace VG.Proof.Rsa

theorem recover_product_exact {d e db eb top : Nat}
    (hd : d < 2 ^ db) (he : e < 2 ^ eb) (fit : db + eb ≤ top) :
    (0 + e % 2 ^ eb * d) % 2 ^ top = d * e := by
  rw [Nat.zero_add, Nat.mod_eq_of_lt he, Nat.mul_comm]
  apply Nat.mod_eq_of_lt
  calc d * e < 2 ^ db * 2 ^ eb := Nat.mul_lt_mul'' hd he
    _ = 2 ^ (db + eb) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ top := Nat.pow_le_pow_right (by decide) fit

end VG.Proof.Rsa
