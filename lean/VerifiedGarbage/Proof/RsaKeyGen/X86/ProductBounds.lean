module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Bounds for unreduced native RSA multiplication

After `i` rows the accumulator is the low `i` words of the first operand
times the second operand. Its window beginning at `i` is smaller than one
second operand's radix. Two carry words therefore suffice for every row.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.Proof.Mont

theorem window_le (m : Mem) (base : Addr) (out total i len : Nat)
    (fits : i + len ≤ total) :
    2 ^ (32 * i) * val32 m base (out + 4 * i) len ≤ val32 m base out total := by
  have split : val32 m base out total = val32 m base out i +
      2 ^ (32 * i) * val32 m base (out + 4 * i) (total - i) := by
    simpa only [Nat.add_sub_of_le (by omega : i ≤ total)] using
      val32_append m base out i (total - i)
  have tail : val32 m base (out + 4 * i) len ≤
      val32 m base (out + 4 * i) (total - i) := by
    have e : total - i = len + (total - i - len) := by omega
    have H := val32_append m base (out + 4 * i) len (total - i - len)
    rw [← e] at H
    omega
  have := Nat.mul_le_mul_left (2 ^ (32 * i)) tail
  omega

theorem row_fits {m : Mem} {base : Addr} {out total i right a b : Nat}
    (fits : i + (right + 2) ≤ total)
    (product : val32 m base out total = val32 m base a i * val32 m base b right) :
    val32 m base (out + 4 * i) (right + 2) +
        w32 m base (a + 4 * i) * val32 m base b right < 2 ^ (32 * (right + 2)) := by
  have B : 0 < 2 ^ (32 * right) := Nat.two_pow_pos _
  have T := window_le m base out total i (right + 2) fits
  rw [product] at T
  have bound : val32 m base a i * val32 m base b right < 2 ^ (32 * i) * 2 ^ (32 * right) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt (val32_lt m base b right)))
      (Nat.mul_lt_mul_of_pos_right (val32_lt m base a i) B)
  have W : val32 m base (out + 4 * i) (right + 2) < 2 ^ (32 * right) := by
    by_cases h : val32 m base (out + 4 * i) (right + 2) < 2 ^ (32 * right)
    · exact h
    · have H := Nat.mul_le_mul_left (2 ^ (32 * i)) (Nat.le_of_not_gt h)
      omega
  have word : w32 m base (a + 4 * i) ≤ 2 ^ 32 - 1 := by
    have H : w32 m base (a + 4 * i) < 2 ^ 32 := (m.readW (off base (a + 4 * i)) 32).isLt
    omega
  have term : w32 m base (a + 4 * i) * val32 m base b right ≤
      (2 ^ 32 - 1) * 2 ^ (32 * right) :=
    Nat.mul_le_mul word (Nat.le_of_lt (val32_lt m base b right))
  rw [Nat.mul_add, Nat.pow_add]
  omega

end VG.Proof.RsaKeyGen.X86.Product
