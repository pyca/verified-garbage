module

public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent, shared verbatim by every architecture's square root by words

/-!
# The square root by words and remainders

What a square root by words, a digit of `β` (`2^64`, or `2^32`) at a time from
the top, computes, against `VG.Spec.Rsa.isqrt`, independent of the target:

* `sqrt_of_rem`: a root `s` and remainder `r` with `s² + r = A` and
  `r ≤ 2 s` are `isqrt A` and `A - (isqrt A)²`; `square_iff_rem`: `A` is a
  square exactly where `r = 0`;
* `step_inv`: a step, the next pair of words `P` brought down and the digit
  `q` the largest with `(2 s β + q) q ≤ r β² + P` (`IsDigit`), keeps the
  invariant; `digit_exists`: every root and number have a digit;
* the digit's bounds: below `β` (`digit_lt`), at most the quotient
  `⌊R / (2 s β)⌋` (`digit_le_div`), and at least that minus one where
  `β ≤ 2 s`, as a normalized root is (`div_le_digit_succ`); so an estimate
  of the quotient at most two above it is at most three above the digit;
* `correction_step`: a correction, `q` down by one, adds `2 s β + 2 q - 1` back;
* `norm_sqrt`, `norm_square`: the root of `4^c X`, shifted down by `c`, is
  that of `X`, and `4^c X` is a square exactly where `X` is, so a normalized
  root needs no other correction.
-/

@[expose] public section

namespace VG.Proof.Bignum.SqrtRem

open VG.Spec.Rsa (isqrt)

/-! ## A root and its remainder -/

/-- A root and remainder with `s² + r = A` and `r ≤ 2 s`: `s` is the root. -/
theorem sqrt_of_rem {s r A : Nat} (h : s * s + r = A) (hr : r ≤ 2 * s) : isqrt A = s :=
  VG.Proof.Rsa.RecoverDet.isqrt_eq (by omega) (by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)

/-- With `s² + r = A` and `r ≤ 2 s`, `A` is a square exactly where `r = 0`. -/
theorem square_iff_rem {s r A : Nat} (h : s * s + r = A) (hr : r ≤ 2 * s) :
    isqrt A * isqrt A = A ↔ r = 0 := by
  rw [sqrt_of_rem h hr]; omega

/-! ## A digit -/

/-- `q` is the digit after root `s` for `R`: the largest with `(2 s β + q) q ≤ R`. -/
def IsDigit (β s R q : Nat) : Prop :=
  (2 * s * β + q) * q ≤ R ∧ R < (2 * s * β + (q + 1)) * (q + 1)

/-- A step keeps the invariant: from `s² + r = A`, `r ≤ 2 s`, the next pair `P`
and its digit `q`, the root `s β + q` and the remainder `R - (2 s β + q) q` of
`A β² + P`, with `R = r β² + P`. -/
theorem step_inv {β s r A P q : Nat} (h : s * s + r = A) (hq : IsDigit β s (r * (β * β) + P) q) :
    (s * β + q) * (s * β + q) + (r * (β * β) + P - (2 * s * β + q) * q) = A * (β * β) + P ∧
      r * (β * β) + P - (2 * s * β + q) * q ≤ 2 * (s * β + q) := by
  obtain ⟨lo, hi⟩ := hq
  have e1 : (s * β + q) * (s * β + q) = s * s * (β * β) + (2 * s * β + q) * q := by grind
  have e2 : (2 * s * β + (q + 1)) * (q + 1) = (2 * s * β + q) * q + (2 * (s * β + q) + 1) := by grind
  rw [e2] at hi
  rw [e1, ← h, Nat.add_mul (s * s) r (β * β)]
  generalize (2 * s * β + q) * q = K at lo hi ⊢
  refine ⟨by omega, by omega⟩

/-- Every root `s` and number `R` have a digit. -/
theorem digit_exists (β s R : Nat) : ∃ q, IsDigit β s R q := by
  have lo := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (s * β * (s * β) + R)
  have hi := VG.Proof.Rsa.RecoverDet.lt_succ_isqrt_sq (s * β * (s * β) + R)
  generalize VG.Spec.Rsa.isqrt (s * β * (s * β) + R) = t at lo hi
  have ht : s * β ≤ t := by
    refine Nat.le_of_not_lt fun h => ?_
    have := Nat.mul_self_le_mul_self (show t + 1 ≤ s * β by omega)
    omega
  obtain ⟨q, rfl⟩ : ∃ q, t = s * β + q := ⟨t - s * β, by omega⟩
  refine ⟨q, ?_, ?_⟩
  · have e : (s * β + q) * (s * β + q) = s * β * (s * β) + (2 * s * β + q) * q := by grind
    omega
  · have e : (s * β + q + 1) * (s * β + q + 1) = s * β * (s * β) + (2 * s * β + (q + 1)) * (q + 1) := by grind
    omega

/-- The digit is below `β` where `r ≤ 2 s` and `P < β²`. -/
theorem digit_lt {β s r P q : Nat} (hr : r ≤ 2 * s) (hP : P < β * β)
    (hq : (2 * s * β + q) * q ≤ r * (β * β) + P) : q < β := by
  refine Nat.lt_of_not_le fun hb => ?_
  have m1 : (2 * s * β + β) * β ≤ (2 * s * β + q) * q :=
    Nat.mul_le_mul (Nat.add_le_add_left hb _) hb
  have m2 : r * (β * β) ≤ 2 * s * β * β := by
    rw [Nat.mul_assoc (2 * s)]; exact Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul] at m1
  omega

/-- The digit is at most the quotient by `2 s β`. -/
theorem digit_le_div {β s R q : Nat} (hd : 0 < 2 * s * β) (hq : (2 * s * β + q) * q ≤ R) :
    q ≤ R / (2 * s * β) := by
  refine (Nat.le_div_iff_mul_le hd).mpr ?_
  have : q * (2 * s * β) ≤ (2 * s * β + q) * q := by
    rw [Nat.mul_comm q]; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  omega

/-- Where `β ≤ 2 s` (a normalized root), the quotient by `2 s β` is at most the digit plus one. -/
theorem div_le_digit_succ {β s R q : Nat} (hβ : β ≤ 2 * s) (hd : 0 < 2 * s * β) (hqβ : q < β)
    (hq : R < (2 * s * β + (q + 1)) * (q + 1)) : R / (2 * s * β) ≤ q + 1 := by
  have hsq : (q + 1) * (q + 1) ≤ 2 * s * β :=
    Nat.le_trans (Nat.mul_le_mul hqβ hqβ) (by rw [Nat.mul_comm (2 * s)]; exact Nat.mul_le_mul_left _ hβ)
  have e : (2 * s * β + (q + 1)) * (q + 1) = 2 * s * β * (q + 1) + (q + 1) * (q + 1) := by grind
  have e' : 2 * s * β * (q + 2) = 2 * s * β * (q + 1) + 2 * s * β := by grind
  have : R < 2 * s * β * (q + 2) := by rw [e'] ; rw [e] at hq; omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm]; exact this))

/-- A correction: the digit down by one adds `2 s β + 2 q - 1` back to the remainder. -/
theorem correction_step (a q : Nat) (hq : 1 ≤ q) :
    (a + q) * q = (a + (q - 1)) * (q - 1) + (a + 2 * q - 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, show a + 2 * (p + 1) - 1 = a + 2 * p + 1 by omega]
  grind

/-! ## Normalization -/

/-- `2^c` divides a root of `4^c X`. -/
theorem two_pow_dvd_of_sq : ∀ (c : Nat) {s X : Nat}, s * s = 4 ^ c * X → 2 ^ c ∣ s
  | 0, _, _, _ => by rw [Nat.pow_zero]; exact Nat.one_dvd _
  | c + 1, s, X, h => by
    have he : s % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one s with e | e
      · exact e
      · exfalso
        have h1 : s * s % 2 = 1 := by rw [Nat.mul_mod, e]
        have h2 : s * s = 4 * (4 ^ c * X) := by rw [h]; grind
        omega
    obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    have ht : t * t = 4 ^ c * X := by
      have : 4 * (t * t) = 4 * (4 ^ c * X) := by rw [show 4 * (t * t) = 2 * t * (2 * t) by grind, h]; grind
      omega
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ c) 2]
    exact Nat.mul_dvd_mul_left 2 (two_pow_dvd_of_sq c ht)

theorem four_pow (c : Nat) : 4 ^ c = 2 ^ c * 2 ^ c := by
  rw [← Nat.mul_pow]

/-- The root of `4^c X`, shifted down by `c`, is that of `X`. -/
theorem norm_sqrt (c X : Nat) : isqrt (4 ^ c * X) / 2 ^ c = isqrt X := by
  have lo := VG.Proof.Rsa.RecoverDet.isqrt_sq_le X
  have hi := VG.Proof.Rsa.RecoverDet.lt_succ_isqrt_sq X
  have lo' := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (4 ^ c * X)
  have hi' := VG.Proof.Rsa.RecoverDet.lt_succ_isqrt_sq (4 ^ c * X)
  generalize isqrt X = t at lo hi ⊢
  generalize isqrt (4 ^ c * X) = s at lo' hi' ⊢
  have p := Nat.two_pow_pos c
  rw [four_pow] at lo' hi'
  -- `s < 2^c (t + 1)`: else `s² ≥ 4^c (t + 1)² > 4^c X`.
  have h1 : s < 2 ^ c * (t + 1) := by
    refine Nat.lt_of_not_le fun hs => ?_
    have := Nat.mul_le_mul hs hs
    have : 2 ^ c * 2 ^ c * X < 2 ^ c * (t + 1) * (2 ^ c * (t + 1)) := by
      rw [show 2 ^ c * (t + 1) * (2 ^ c * (t + 1)) = 2 ^ c * 2 ^ c * ((t + 1) * (t + 1)) by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]]
      exact Nat.mul_lt_mul_of_pos_left hi (Nat.mul_pos p p)
    omega
  -- `2^c t ≤ s`: else `(s + 1)² ≤ 4^c t² ≤ 4^c X`.
  have h2 : 2 ^ c * t ≤ s := by
    refine Nat.le_of_not_lt fun hs => ?_
    have h' : s + 1 ≤ 2 ^ c * t := by omega
    have := Nat.mul_le_mul h' h'
    have : 2 ^ c * t * (2 ^ c * t) ≤ 2 ^ c * 2 ^ c * X := by
      rw [show 2 ^ c * t * (2 ^ c * t) = 2 ^ c * 2 ^ c * (t * t) by simp only [Nat.mul_assoc, Nat.mul_left_comm]]
      exact Nat.mul_le_mul_left _ lo
    omega
  exact Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h2) (by rw [Nat.mul_comm]; exact h1)

/-- `4^c X` is a square exactly where `X` is. -/
theorem norm_square (c X : Nat) :
    isqrt (4 ^ c * X) * isqrt (4 ^ c * X) = 4 ^ c * X ↔ isqrt X * isqrt X = X := by
  have p := Nat.two_pow_pos c
  constructor
  · intro h
    obtain ⟨t, ht⟩ := two_pow_dvd_of_sq c h
    have e : t * t = X := by
      rw [ht, four_pow] at h
      have : 2 ^ c * 2 ^ c * (t * t) = 2 ^ c * 2 ^ c * X := by
        rw [← h]; simp only [Nat.mul_assoc, Nat.mul_left_comm]
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos p p) this
    rw [← norm_sqrt c X, ht, Nat.mul_div_cancel_left _ p]; exact e
  · intro h
    have e : isqrt (4 ^ c * X) = 2 ^ c * isqrt X := by
      refine sqrt_of_rem (r := 0) ?_ (Nat.zero_le _)
      rw [Nat.add_zero, four_pow]
      conv => rhs; rw [← h]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [e, four_pow]
    conv => rhs; rw [← h]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]

end VG.Proof.Bignum.SqrtRem
