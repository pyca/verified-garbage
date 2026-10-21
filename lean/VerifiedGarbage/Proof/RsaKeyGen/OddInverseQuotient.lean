module

public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.KeyInv

/-! # The quotient-based private exponent with an exact small correction

For `L = e*Q + R` and `x*R ≡ 1 mod e`, the private exponent is
`Q*(e-x) + (R*(e-x)+1)/e`. The correction fits the public exponent's
width. Its numerator needs at most 128 bits for any 64-bit exponent.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen

def oddQuotient (e Q R x : Nat) : Nat := Q * (e - x) + (R * (e - x) + 1) / e

theorem odd_correction_le {e R x : Nat} (positive : 2 ≤ e) : (R * (e - x) + 1) / e ≤ R := by
  have product := Nat.mul_le_mul_left R (Nat.sub_le e x)
  have numerator : R * (e - x) + 1 < (R + 1) * e := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have bound : (R * (e - x) + 1) / e < R + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr numerator
  omega

theorem oddQuotient_le {e L Q R x : Nat} (positive : 2 ≤ e) (division : L = e * Q + R) :
    oddQuotient e Q R x ≤ L := by
  have product := Nat.mul_le_mul_left Q (Nat.sub_le e x)
  have correction := odd_correction_le (R := R) (x := x) positive
  rw [Nat.mul_comm Q e] at product
  unfold oddQuotient
  omega

theorem oddQuotient_inverse {e L Q R x : Nat} (positive : 3 ≤ e) (large : 2 ≤ L)
    (division : L = e * Q + R) (inverse : (e : Int) ∣ (x : Int) * R - 1) (bound : x < e) :
    Spec.Rsa.inverse e L = some (oddQuotient e Q R x) := by
  have identity : (x : Int) * L - 1 = (e : Int) * ((x : Int) * Q) + ((x : Int) * R - 1) := by
    rw [division]
    push_cast
    rw [Int.mul_add, Int.mul_left_comm (x : Int) (e : Int) (Q : Int), Int.add_sub_assoc]
  have inverseL : (e : Int) ∣ (x : Int) * L - 1 := by
    rw [identity]
    exact Int.dvd_add (Int.dvd_mul_right _ _) inverse
  have result := (inverse_odd_exact positive large inverseL bound).2
  have numerator : L * (e - x) + 1 = e * (Q * (e - x)) + (R * (e - x) + 1) := by
    rw [division]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  rw [numerator, Nat.mul_add_div (by omega)] at result
  exact result

theorem odd_correction_fits {e R x : Nat} (positive : 2 ≤ e) (exponent : e < 2 ^ 64) (remainder : R < e) :
    (R * (e - x) + 1) / e < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (odd_correction_le positive) (Nat.lt_trans remainder exponent)

theorem odd_numerator_fits {e R x : Nat} (exponent : e < 2 ^ 64) (remainder : R < e) :
    R * (e - x) + 1 < 2 ^ 128 := by
  have left : R ≤ 2 ^ 64 - 1 := by omega
  have right : e - x ≤ 2 ^ 64 - 1 := by omega
  have product := Nat.mul_le_mul left right
  omega

end VG.Proof.RsaKeyGen
