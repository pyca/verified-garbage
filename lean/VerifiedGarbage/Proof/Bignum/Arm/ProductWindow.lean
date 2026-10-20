module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Lift a native multiply-add row into the complete wide product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem product_window_lift {m m' : Mem} {base : Addr} {o i n k delta : Nat}
    (fit : i + n ≤ k) (addressFit : o + 4 * k ≤ 2 ^ 64)
    (outside : Outside base (o + 4 * i) (4 * n) m m')
    (row : val32 m' base (o + 4 * i) n = val32 m base (o + 4 * i) n + delta) :
    val32 m' base o k = val32 m base o k + 2 ^ (32 * i) * delta := by
  have low := outside.val32 (d := o) (k := i) (by omega) (by omega)
  have high := outside.val32 (d := o + 4 * (i + n)) (k := k - (i + n)) (by omega) (by omega)
  rw [show k = i + (n + (k - (i + n))) by omega, val32_append m' base o i, val32_append m base o i,
    val32_append m' base (o + 4 * i) n, val32_append m base (o + 4 * i) n,
    show o + 4 * i + 4 * n = o + 4 * (i + n) by omega, low, high, row]
  simp only [Nat.mul_add]
  omega

theorem product_window_bound {m : Mem} {base : Addr} {o i n k A B : Nat}
    (fit : i + (n + 2) ≤ k) (value : val32 m base o k = A * B)
    (aBound : A < 2 ^ (32 * i)) (bBound : B < 2 ^ (32 * n)) :
    val32 m base (o + 4 * i) (n + 2) < 2 ^ (32 * n) := by
  have split := val32_append m base o i (n + 2 + (k - (i + (n + 2))))
  rw [show i + (n + 2 + (k - (i + (n + 2)))) = k by omega,
    val32_append m base (o + 4 * i) (n + 2)] at split
  have low : 2 ^ (32 * i) * val32 m base (o + 4 * i) (n + 2) ≤ val32 m base o k := by
    rw [split, Nat.mul_add]
    omega
  have bound : A * B < 2 ^ (32 * i) * 2 ^ (32 * n) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right B (Nat.le_of_lt aBound))
      (Nat.mul_lt_mul_of_pos_left bBound (Nat.two_pow_pos _))
  rw [value] at low
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt low bound)

end VG.Proof.Bignum.Arm
