module

public import VerifiedGarbage.Proof.Bignum.WideWindow

/-! # Schoolbook partial products fit the row accumulator -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem wide_window_bound {s t : Mem} {base : Addr} {N out a b i : Nat}
    (hi : i < N)
    (V : val32 t base out (2 * N + 1) = val32 s base a i * val32 s base b N) :
    val32 t base (out + 4 * i) (N + 2) ≤ val32 s base b N := by
  have split := val32_append t base out i (N + 2 + (N - 1 - i))
  rw [show i + (N + 2 + (N - 1 - i)) = 2 * N + 1 by omega,
    val32_append t base (out + 4 * i), Nat.mul_add] at split
  have low : 2 ^ (32 * i) * val32 t base (out + 4 * i) (N + 2) ≤ val32 t base out (2 * N + 1) := by omega
  have high : val32 t base out (2 * N + 1) ≤ 2 ^ (32 * i) * val32 s base b N := by
    rw [V]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt (val32_lt _ _ _ _))
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans low high) (Nat.two_pow_pos _)

theorem wide_row_bound {s t : Mem} {base : Addr} {N out a b i : Nat}
    (hi : i < N)
    (V : val32 t base out (2 * N + 1) = val32 s base a i * val32 s base b N) :
    val32 t base (out + 4 * i) (N + 2) + w32 s base (a + 4 * i) * val32 s base b N <
      2 ^ (32 * (N + 2)) := by
  have win := wide_window_bound hi V
  have digit : w32 s base (a + 4 * i) < 2 ^ 32 := (s.readW _ 32).isLt
  have row := Nat.mul_le_mul_right (val32 s base b N) (show w32 s base (a + 4 * i) + 1 ≤ 2 ^ 32 by omega)
  rw [Nat.add_mul, Nat.one_mul] at row
  have bound := Nat.mul_lt_mul_of_pos_left (val32_lt s base b N) (by decide : 0 < 2 ^ 32)
  have room : 2 ^ 32 * 2 ^ (32 * N) ≤ 2 ^ (32 * (N + 2)) := by
    rw [← pow32_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

end VG.Proof.Bignum
