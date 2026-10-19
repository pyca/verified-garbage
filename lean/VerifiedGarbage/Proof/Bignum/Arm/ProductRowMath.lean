module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.Arm.ProductWindow
import VerifiedGarbage.Proof.Bignum.Arm.RowFull

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
  omega

theorem product_row_value {m m' original : Mem} {base : Addr} {o a b i n k : Nat}
    (fit : i + (n + 2) ≤ k) (addressFit : o + 4 * k ≤ 2 ^ 64)
    (outside : Outside base (o + 4 * i) (4 * (n + 2)) m m')
    (value : val32 m base o k = val32 original base a i * val32 original base b n)
    (row : val32 m' base (o + 4 * i) (n + 2) = val32 m base (o + 4 * i) (n + 2) +
      w32 original base (a + 4 * i) * val32 original base b n) :
    val32 m' base o k = val32 original base a (i + 1) * val32 original base b n := by
  rw [product_window_lift fit addressFit outside row, value, val32_succ, Nat.add_mul, Nat.mul_assoc]

end VG.Proof.Bignum.Arm
