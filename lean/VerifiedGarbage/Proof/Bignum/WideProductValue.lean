module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # A full product occupies exactly twice the operand width -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem wide_product_value {s t : Mem} {base : Addr} {N out a b : Nat}
    (V : val32 t base out (2 * N + 1) = val32 s base a N * val32 s base b N) :
    val32 t base out (2 * N) = val32 s base a N * val32 s base b N := by
  have bound : val32 s base a N * val32 s base b N < 2 ^ (32 * (2 * N)) := by
    have H := Nat.mul_lt_mul_of_lt_of_le (val32_lt s base a N)
      (Nat.le_of_lt (val32_lt s base b N)) (Nat.two_pow_pos (32 * N))
    rw [← Nat.pow_add, show 32 * N + 32 * N = 32 * (2 * N) by omega] at H
    exact H
  rw [val32_succ] at V
  have low := val32_lt t base out (2 * N)
  have top : w32 t base (out + 4 * (2 * N)) = 0 := by
    by_contra H
    have positive : 1 ≤ w32 t base (out + 4 * (2 * N)) := by omega
    have := Nat.mul_le_mul_left (2 ^ (32 * (2 * N))) positive
    omega
  rw [top, Nat.mul_zero, Nat.add_zero] at V
  exact V

end VG.Proof.Bignum
