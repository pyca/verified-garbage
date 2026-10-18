module

public import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bounds for the full private exponent in RSA key validation -/

@[expose] public section

namespace VG.Proof.Rsa

/-- A bound expressed only through the other factor's public byte length. -/
theorem fullExp_bound {e d x y L : Nat} (he : e < 2 ^ 33) (hx : 2 ≤ x)
    (hd : d < x * y) (hy : y < 2 ^ (64 * ((L + 7) / 8))) :
    e * d < 2 ^ (64 * ((L + 7) / 8 + 1)) * (x - 1) := by
  have hx' : x ≤ 2 * (x - 1) := by omega
  have hxy : x * y ≤ 2 * (x - 1) * y := Nat.mul_le_mul_right y hx'
  have hed : e * d ≤ e * (2 * (x - 1) * y) := Nat.mul_le_mul_left e (by omega)
  have hey : e * y < 2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)) := Nat.mul_lt_mul_of_lt_of_lt he hy
  have hsmall : 2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8))) ≤ 2 ^ (64 * ((L + 7) / 8 + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (2 ^ (64 * ((L + 7) / 8))) (show 2 * 2 ^ 33 ≤ (2 : Nat) ^ 64 by decide)
  have hpos : 0 < x - 1 := by omega
  calc e * d ≤ (2 * (e * y)) * (x - 1) := by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hed
    _ < (2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)))) * (x - 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hey (by decide)) hpos
    _ ≤ _ := Nat.mul_le_mul_right _ hsmall

end VG.Proof.Rsa
