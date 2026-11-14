module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32

/-!
# The top words of a normalized number, by 32-bit words

Target-independent (x86's and ARMv7's word steps; the same lemmas as x86's
`R2Words/Step.lean`): a number's top words (`val32_top3`, `val32_top2`), the
top three and two words of `2^z x` from `x`'s by products with `2^z`
(`top3_math`, `top_math`), the top bit (`topBit_iff`), and the 2-by-1
estimate with `u₂ = d` (`qhat_min`).
-/

@[expose] public section

namespace VG.Proof.Bignum.WordTop32

open VG.Proof.Mont VG.Proof.Bignum.WordStep32

/-- A number of `k + 3` words as its top three words and the rest. -/
theorem val32_top3 (m : Mem) (base : Addr) (o k : Nat) :
    val32 m base o (k + 3) = val32 m base o k + 2 ^ (32 * k) * w32 m base (o + 4 * k) +
      2 ^ (32 * k) * 2 ^ 32 * (w32 m base (o + 4 * (k + 1)) + 2 ^ 32 * w32 m base (o + 4 * (k + 2))) := by
  rw [show k + 3 = k + 1 + 1 + 1 from rfl, val32_succ, val32_succ, val32_succ,
    show 32 * (k + 1 + 1) = 32 * k + 32 + 32 by omega_using [], show 32 * (k + 1) = 32 * k + 32 by omega_using [],
    Nat.pow_add, Nat.pow_add, show k + 1 + 1 = k + 2 from rfl]
  grind

/-- A number of `k + 2` words as its top two words and the rest. -/
theorem val32_top2 (m : Mem) (base : Addr) (o k : Nat) :
    val32 m base o (k + 2) = val32 m base o k + 2 ^ (32 * k) * (w32 m base (o + 4 * k) +
      2 ^ 32 * w32 m base (o + 4 * (k + 1))) := by
  rw [show k + 2 = k + 1 + 1 from rfl, val32_succ, val32_succ, show 32 * (k + 1) = 32 * k + 32 by omega_using [], Nat.pow_add]
  grind

/-- The top word `a₁` of `x` shifted, `a₁ 2^z < 2^32`, for `2^z x < 2^(32 (k + 3))`. -/
theorem top_small {L k a1 a2 a3 z : Nat}
    (htop : (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z < 2 ^ (32 * (k + 3))) :
    a1 * 2 ^ z < 2 ^ 32 := by
  have e : 2 ^ (32 * (k + 3)) = 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * 2 ^ 32 := by
    rw [show 32 * (k + 3) = 32 * k + 32 + 32 + 32 by omega_using [], Nat.pow_add, Nat.pow_add, Nat.pow_add]
  rw [e] at htop
  have h2 : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * (a1 * 2 ^ z) ≤
      (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z := by
    have : 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 * a1 ≤ L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
      rw [Nat.mul_add (2 ^ (32 * k) * 2 ^ 32), Nat.mul_assoc (2 ^ (32 * k) * 2 ^ 32) (2 ^ 32)]; omega_using []
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ this
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h2 htop)

/-- The top three words `(u₂, u₁, u₀)` of `2^z x`, from `x`'s top four words
`a₁`, `a₂`, `a₃`, `a`, for `a₁ 2^z < 2^32`. -/
theorem top3_math {L k a a1 a2 a3 z : Nat} (hz : z ≤ 31) (hL : L < 2 ^ (32 * k)) (h1 : a1 * 2 ^ z < 2 ^ 32) :
    (a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32) * 2 ^ 64 + (a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32) * 2 ^ 32 +
        (a3 * 2 ^ z % 2 ^ 32 + a * 2 ^ z / 2 ^ 32) =
      (L + 2 ^ (32 * k) * a + 2 ^ (32 * k) * 2 ^ 32 * (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1)) * 2 ^ z /
        (2 ^ (32 * k) * 2 ^ 32) := by
  have e : (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1) * 2 ^ z = a3 * 2 ^ z + 2 ^ 32 * (a2 * 2 ^ z) + 2 ^ 64 * (a1 * 2 ^ z) := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  rw [shl_div (by omega_using [hz]) hL, e, Nat.mod_eq_of_lt h1]
  have h2 := Nat.div_add_mod (a2 * 2 ^ z) (2 ^ 32)
  have h3 := Nat.div_add_mod (a3 * 2 ^ z) (2 ^ 32)
  generalize a * 2 ^ z / 2 ^ 32 = hA
  generalize a1 * 2 ^ z = A1 at *
  generalize a2 * 2 ^ z = A2 at *
  generalize a3 * 2 ^ z = A3 at *
  omega_using []

/-- The top two words `u₂ 2^32 + u₁` of `2^z x`, from `x`'s top three words
`a₁`, `a₂`, `a₃`, for `2^z x < 2^(32 (k + 3))`. -/
theorem top_math {L k a1 a2 a3 z : Nat} (hz : z ≤ 31) (hL : L < 2 ^ (32 * k))
    (htop : (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z < 2 ^ (32 * (k + 3))) :
    (a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32) * 2 ^ 32 + (a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32) =
      (L + 2 ^ (32 * k) * a3 + 2 ^ (32 * k) * 2 ^ 32 * (a2 + 2 ^ 32 * a1)) * 2 ^ z / 2 ^ (32 * (k + 1)) := by
  have hK := Nat.two_pow_pos (32 * k)
  rw [show 32 * (k + 1) = 32 * k + 32 by omega_using [], Nat.pow_add, shl_div (by omega_using [hz]) hL]
  have h1 : a1 * 2 ^ z < 2 ^ 32 := top_small htop
  have hd := Nat.div_add_mod (a2 * 2 ^ z) (2 ^ 32)
  rw [Nat.mod_eq_of_lt h1]
  grind

/-- The top bit of a number of `w + 1` words. -/
theorem topBit_iff {low top w : Nat} (hl : low < 2 ^ (32 * w)) (ht : top < 2 ^ 32) :
    (2 ^ (32 * (w + 1)) / 2 ≤ low + 2 ^ (32 * w) * top) ↔ 2 ^ 31 ≤ top := by
  have e : 2 ^ (32 * (w + 1)) / 2 = 2 ^ (32 * w) * 2 ^ 31 := by
    rw [show 32 * (w + 1) = 32 * w + 31 + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.pow_add]
  rw [e]
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hc => ?_
    have := Nat.mul_le_mul_left (2 ^ (32 * w)) (show top + 1 ≤ 2 ^ 31 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro h; have := Nat.mul_le_mul_left (2 ^ (32 * w)) h; omega

/-- `quot`'s estimate is `min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)`. -/
theorem qhat_min {u2 u1 d : Nat} (hu : u2 ≤ d) (hu1 : u1 < 2 ^ 32) (hd : 0 < d) :
    (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) = min ((u2 * 2 ^ 32 + u1) / d) (2 ^ 32 - 1) := by
  by_cases e : u2 = d
  · rw [ite_eq_left e, Nat.min_eq_right]
    rw [e, Nat.le_div_iff_mul_le hd]
    have : (2 ^ 32 - 1) * d ≤ 2 ^ 32 * d := Nat.mul_le_mul_right d (Nat.sub_le _ _)
    rw [Nat.mul_comm d]; omega_using []
  · rw [ite_eq_right e, Nat.min_eq_left]
    have : (u2 * 2 ^ 32 + u1) / d < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have := Nat.mul_le_mul_right (2 ^ 32) (show u2 + 1 ≤ d by omega_using [hu, e])
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm d] at this; omega_using [hu, hu1, e]
    omega_using [this]

end VG.Proof.Bignum.WordTop32
