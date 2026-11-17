module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Bignum.Arm.ProductWindow`, which this module and modules that import it used -/

section

/-! # Lift a native multiply-add row into the complete wide product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem product_window_lift {m m' : Mem} {base : Addr} {o i n k delta : Nat}
    (fit : i + n ≤ k) (addressFit : o + 4 * k ≤ 2 ^ 64)
    (outside : Outside base (o + 4 * i) (4 * n) m m')
    (row : val32 m' base (o + 4 * i) n = val32 m base (o + 4 * i) n + delta) :
    val32 m' base o k = val32 m base o k + 2 ^ (32 * i) * delta := by
  have low := outside.val32 (d := o) (k := i) (by omega_using []) (by omega_using [fit, addressFit])
  have high := outside.val32 (d := o + 4 * (i + n)) (k := k - (i + n)) (by omega_using []) (by omega_using [fit, addressFit])
  rw [show k = i + (n + (k - (i + n))) by omega_using [fit], val32_append m' base o i, val32_append m base o i,
    val32_append m' base (o + 4 * i) n, val32_append m base (o + 4 * i) n,
    show o + 4 * i + 4 * n = o + 4 * (i + n) by omega_using [], low, high, row]
  simp only [Nat.mul_add]
  omega_using []

theorem product_window_bound {m : Mem} {base : Addr} {o i n k A B : Nat}
    (fit : i + (n + 2) ≤ k) (value : val32 m base o k = A * B)
    (aBound : A < 2 ^ (32 * i)) (bBound : B < 2 ^ (32 * n)) :
    val32 m base (o + 4 * i) (n + 2) < 2 ^ (32 * n) := by
  have split := val32_append m base o i (n + 2 + (k - (i + (n + 2))))
  rw [show i + (n + 2 + (k - (i + (n + 2)))) = k by omega_using [fit],
    val32_append m base (o + 4 * i) (n + 2)] at split
  have low : 2 ^ (32 * i) * val32 m base (o + 4 * i) (n + 2) ≤ val32 m base o k := by
    rw [split, Nat.mul_add]
    omega_using []
  have bound : A * B < 2 ^ (32 * i) * 2 ^ (32 * n) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right B (Nat.le_of_lt aBound))
      (Nat.mul_lt_mul_of_pos_left bBound (Nat.two_pow_pos _))
  rw [value] at low
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt low bound)

end VG.Proof.Bignum.Arm

end

end

/-! # Bounds and positional value of a native wide-product row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem product_row_fits {acc scalar B n : Nat}
    (accBound : acc < 2 ^ (32 * n)) (scalarBound : scalar < 2 ^ 32) (bBound : B < 2 ^ (32 * n)) :
    acc + scalar * B < 2 ^ (32 * (n + 2)) := by
  have bound := Nat.mul_le_mul (Nat.le_of_lt scalarBound) (Nat.le_of_lt bBound)
  rw [pow32_addtwo]
  have positive := Nat.two_pow_pos (32 * n)
  omega_using [accBound, bound]

theorem product_row_value {m m' original : Mem} {base : Addr} {o a b i n k : Nat}
    (fit : i + (n + 2) ≤ k) (addressFit : o + 4 * k ≤ 2 ^ 64)
    (outside : Outside base (o + 4 * i) (4 * (n + 2)) m m')
    (value : val32 m base o k = val32 original base a i * val32 original base b n)
    (row : val32 m' base (o + 4 * i) (n + 2) = val32 m base (o + 4 * i) (n + 2) +
      w32 original base (a + 4 * i) * val32 original base b n) :
    val32 m' base o k = val32 original base a (i + 1) * val32 original base b n := by
  rw [product_window_lift fit addressFit outside row, value, val32_succ, Nat.add_mul, Nat.mul_assoc]

end VG.Proof.Bignum.Arm
