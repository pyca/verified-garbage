module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Signed multiword numbers and their shift right by 59

`sgn L x`: the two's complement value of a number of `L` 64-bit words.
The arithmetic shift right by 59 of such a number a word at a time: word
`j` of the result from words `j` and `j + 1` (`extr59`), the invariant
after `j` words (`shr_step`: the number read is its low 59 bits, `2^59`
times the words written, and the rest of word `j`), and the top word from
the sign (`shr_final`: `2^59 sgn O + lo = sgn S`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- The two's complement value of a number of `L` words. -/
def sgn (L x : Nat) : Int := if x < 2 ^ (64 * L - 1) then (x : Int) else (x : Int) - 2 ^ (64 * L)

/-- A step of the shift by 59: the invariant for `j + 1` words from `j`. -/
theorem shr_step {W O lo P s0 s1 o : Nat} (h : W = lo + 2 ^ 59 * O + P * 2 ^ 59 * (s0 / 2 ^ 59))
    (ho : o = s0 / 2 ^ 59 + 2 ^ 5 * (s1 % 2 ^ 59)) :
    W + P * 2 ^ 64 * s1 = lo + 2 ^ 59 * (O + P * o) + P * 2 ^ 64 * 2 ^ 59 * (s1 / 2 ^ 59) := by
  have := Nat.div_add_mod s1 (2 ^ 59)
  subst h ho
  grind

/-- A word of the shift: `(s0 + 2^64 s1) >> 59` modulo `2^64`. -/
theorem extr59 (s0 s1 : BitVec 64) :
    ((s1 ++ s0).extractLsb' 59 64).toNat = s0.toNat / 2 ^ 59 + 2 ^ 5 * (s1.toNat % 2 ^ 59) := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt s0.isLt, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := s0.isLt; have := s1.isLt
  omega
theorem pow_half {L : Nat} (hL : 1 ≤ L) : 2 ^ (64 * L) = 2 * 2 ^ (64 * L - 1) ∧ 2 ^ 63 ≤ 2 ^ (64 * L - 1) := by
  refine ⟨?_, Nat.pow_le_pow_right (by decide) (by omega)⟩
  rw [← Nat.pow_succ']; congr 1; omega

/-- The end of the shift by 59: the top word from the sign mask `M`. -/
theorem shr_final {S O lo L M : Nat} (hL : 1 ≤ L) (hS : S < 2 ^ (64 * L)) (hO : O < 2 ^ (64 * L))
    (hlo : lo < 2 ^ 59) (hM : M = if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1)
    (h : S + 2 ^ (64 * L) * M = lo + 2 ^ 59 * O + 2 ^ (64 * L) * 2 ^ 59 * (M / 2 ^ 59)) :
    2 ^ 59 * sgn L O + lo = sgn L S := by
  obtain ⟨e, h63⟩ := pow_half hL
  unfold sgn
  rw [show (2 : Int) ^ (64 * L) = ((2 ^ (64 * L) : Nat) : Int) by push_cast; rfl, e]
  rw [e] at hS hO h
  generalize 2 ^ (64 * L - 1) = H at *
  split at hM <;> subst hM
  · rw [Nat.zero_div, Nat.mul_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at h
    rw [ite_eq_left (by omega : S < H)]; split <;> omega
  · rw [show (2 ^ 64 - 1) / 2 ^ 59 = 31 by decide] at h
    rw [ite_eq_right (by omega : ¬ S < H)]; split <;> omega

/-- The sign of a number of `n + 1` words is its top word's. -/
theorem top_sign {W s n : Nat} (hW : W < 2 ^ (64 * n)) (hs : s < 2 ^ 64) :
    W + 2 ^ (64 * n) * s < 2 ^ (64 * (n + 1) - 1) ↔ s < 2 ^ 63 := by
  have e : 2 ^ (64 * (n + 1) - 1) = 2 ^ (64 * n) * 2 ^ 63 := by
    rw [← Nat.pow_add]; congr 1
  rw [e]
  constructor
  · intro h
    exact Nat.lt_of_not_le fun hc => by
      have := Nat.mul_le_mul_left (2 ^ (64 * n)) hc
      omega
  · intro h
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show s ≤ 2 ^ 63 - 1 by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 63 := Nat.le_mul_of_pos_right _ (by decide)
    omega

end VG.Proof.Divstep
