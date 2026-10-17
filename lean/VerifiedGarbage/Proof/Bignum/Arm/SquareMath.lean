module

public import VerifiedGarbage.Proof.Mont.Words32
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The arithmetic of ARMv7 Montgomery squaring

The square of `a = Σ a_i 2^(32 i)` is its words' squares at the even
positions plus twice the cross products `a_i a_j` (`i < j`), which the rows
`a_i a[i+1 …]` add once each. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

/-- The first `k` rows of cross products: `Σ_{i<k} 2^(32 (2i+1)) a_i a[i+1 … n−1]`. -/
def sqCross (m : Mem) (base : Addr) (a n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sqCross m base a n k +
      2 ^ (32 * (2 * k + 1)) * (w32 m base (a + 4 * k) * val32 m base (a + 4 * (k + 1)) (n - 1 - k))

/-- The squares of the first `k` words, at the positions `2i`. -/
def diagSum (m : Mem) (base : Addr) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => diagSum m base a k + 2 ^ (64 * k) * (w32 m base (a + 4 * k) * w32 m base (a + 4 * k))

theorem sq_split (m : Mem) (base : Addr) (a n : Nat) : ∀ k, k ≤ n →
    val32 m base a n * val32 m base a n = diagSum m base a k + 2 * sqCross m base a n k +
      2 ^ (64 * k) * (val32 m base (a + 4 * k) (n - k) * val32 m base (a + 4 * k) (n - k))
  | 0, _ => by simp only [diagSum, sqCross, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.sub_zero]
  | k + 1, hk => by
    rw [sq_split m base a n k (by omega)]
    have e : n - k = (n - 1 - k) + 1 := by omega
    rw [e, val32, show a + 4 * k + 4 = a + 4 * (k + 1) by omega, show n - (k + 1) = n - 1 - k by omega]
    simp only [diagSum, sqCross]
    have e1 : 2 ^ (32 * (2 * k + 1)) = 2 ^ (64 * k) * 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1 <;> omega
    have e2 : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 32 * 2 ^ 32 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1 <;> omega
    rw [e1, e2]
    generalize w32 m base (a + 4 * k) = x
    generalize val32 m base (a + 4 * (k + 1)) (n - 1 - k) = y
    generalize 2 ^ (64 * k) = P
    generalize (2 : Nat) ^ 32 = W
    grind

theorem sq_eq (m : Mem) (base : Addr) (a n : Nat) :
    val32 m base a n * val32 m base a n = diagSum m base a n + 2 * sqCross m base a n n := by
  rw [sq_split m base a n n (Nat.le_refl _), Nat.sub_self]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

/-- The last row is empty. -/
theorem sqCross_last (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    sqCross m base a n n = sqCross m base a n (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [sqCross, Nat.add_sub_cancel, Nat.sub_self, val32, Nat.mul_zero, Nat.add_zero]

/-- Replacing the middle `j` words of `i + j + k`. -/
theorem val32_replace {m m' : Mem} {base : Addr} {d i j k : Nat}
    (lo : val32 m' base d i = val32 m base d i)
    (hi : val32 m' base (d + 4 * (i + j)) k = val32 m base (d + 4 * (i + j)) k) :
    val32 m' base d (i + j + k) + 2 ^ (32 * i) * val32 m base (d + 4 * i) j =
      val32 m base d (i + j + k) + 2 ^ (32 * i) * val32 m' base (d + 4 * i) j := by
  rw [val32_append m' base d (i + j) k, val32_append m base d (i + j) k, val32_append m' base d i j,
    val32_append m base d i j, lo, hi]
  grind

/-- The value after `n` reductions: below `2m` for an operand below `m < 2^(32 n)`. -/
theorem sq_red_bound {x M Q H R : Nat} (hx : x < M) (hM : M ≤ R) (hQ : Q < R)
    (h : R * H = x * x + Q * M) : H < 2 * M := by
  have h1 : x * x ≤ x * M := Nat.mul_le_mul_left _ (Nat.le_of_lt hx)
  have h2 : x * M < R * M := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le hx hM)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hx)
  have h3 : Q * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt hQ)
  have h4 : R * H < R * (2 * M) := by
    rw [h, Nat.mul_comm 2 M, ← Nat.mul_assoc, Nat.mul_two]
    omega
  exact Nat.lt_of_mul_lt_mul_left h4

end VG.Proof.Bignum.Arm
