module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The reciprocal of a word, from where it stops

For a word `d ≥ 2^63`, `v = ⌊(2^128 - 1) / d⌋ - 2^64` is the largest `v`
with `(2^64 + v) d < 2^128`. Code that corrects some guess of `v` one at a
time, down while `over v d` (`(2^64 + v) d ≥ 2^128`, from the carry of
`d + ⌊v d / 2^64⌋`) and then up while `up v d`, stops at that `v`
(`recip_exact`): its correctness needs no bound on the guess.
-/

@[expose] public section

namespace VG.Proof.Bignum.Recip

/-- Whether `(2^64 + v) d ≥ 2^128`, as code can test it: the carry of
`d + ⌊v d / 2^64⌋`. -/
def over (v D : Nat) : Bool := decide (2 ^ 64 ≤ v * D / 2 ^ 64 + D)

/-- Whether to raise `v`: `v + 1` is a word and `(2^64 + v + 1) d < 2^128`. -/
def up (v D : Nat) : Bool := !decide (v + 1 = 2 ^ 64) && !over (v + 1) D

theorem over_pos {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = true) : 1 ≤ v := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  unfold over at h
  rw [h0, Nat.zero_mul, Nat.zero_div, Nat.zero_add, decide_eq_true_eq] at h
  omega_using [h, hD]

/-- `over v d` is false iff `(2^64 + v) d < 2^128`. -/
theorem over_false {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = false) : 2 ^ 64 * D + v * D < 2 ^ 128 := by
  unfold over at h
  rw [decide_eq_false_iff_not, Nat.not_le, ← Nat.lt_sub_iff_add_lt, Nat.div_lt_iff_lt_mul (by decide)] at h
  have : (2 ^ 64 - D) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D := by
    rw [Nat.sub_mul, Nat.mul_comm D]
  omega_using [h, this, hD]

theorem over_true {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = true) : 2 ^ 128 ≤ 2 ^ 64 * D + v * D := by
  unfold over at h
  rw [decide_eq_true_eq, ← Nat.sub_le_iff_le_add, Nat.le_div_iff_mul_le (by decide)] at h
  have : (2 ^ 64 - D) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D := by
    rw [Nat.sub_mul, Nat.mul_comm D]
  omega_using [h, this, hD]

/-- The largest `v` with `(2^64 + v) d < 2^128` is `v = ⌊(2^128 - 1) / d⌋ - 2^64`. -/
theorem recip_exact {v D : Nat} (hd : 2 ^ 63 ≤ D) (hD : D < 2 ^ 64) (ho : over v D = false) (hu : up v D = false) : v = (2 ^ 128 - 1) / D - 2 ^ 64 := by
  have h1 := over_false hD ho
  have h2 : 2 ^ 128 ≤ 2 ^ 64 * D + (v + 1) * D := by
    unfold up at hu
    rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', decide_eq_true_eq] at hu
    rcases hu with h | h
    · rw [h]; omega_using [hd]
    · exact over_true hD h
  rw [Nat.add_mul, Nat.one_mul] at h2
  have e : (2 ^ 128 - 1) / D = 2 ^ 64 + v := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.add_mul]; omega_using [h1]
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega_using [h2]
  omega_using [e]

end VG.Proof.Bignum.Recip
