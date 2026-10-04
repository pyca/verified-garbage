import VerifiedGarbage.Proof.X448.BaseTable
import Mathlib.Algebra.Module.NatInt

/-!
# The fixed-base comb's digits and partial sums

As `Proof/Ed25519/CombDigits.lean` for Ed25519's comb, for 448 bits. The
scalar `S < 256^56` has 112 nibbles `n_i`; the digits are `d_i = n_i - 8`, from
`-8` to `7`. Step `j < 56` adds `d_{2j+1} 256^j` to one accumulator and
`d_{2j} 256^j` to another, both starting at `G = baseGVal`; 16 times the first
plus the second is `S` (`comb_total`), since `G = 8 Σ_{j < 56} 256^j`.

A negative digit adds the negation `(-x, y)` of the table entry `|d|`
(`baseEntry_ok`).
-/

namespace VG.Proof.X448

open VG.Impl.X448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open Spec.X448 (Fe)

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

theorem pow_256 (n : Nat) : 256 ^ n = 16 ^ (2 * n) := by
  rw [Nat.pow_mul]

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, pow_256]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega
    rw [this]; ring

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

theorem baseGVal_eq : baseGVal = 8 * geom 56 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The two accumulators' multiples of `B` give the scalar: `16 (G + Σ_j d_{2j+1} 256^j) +
(G + Σ_j d_{2j} 256^j) = S`. -/
theorem comb_total {S : Nat} (hS : S < 256 ^ 56) :
    16 * ((baseGVal : ℤ) + oddSumZ S 56) + (baseGVal + evenSumZ S 56) = S := by
  simp only [oddSumZ_eq, evenSumZ_eq, baseGVal_eq]
  have h := comb_partial S 56
  rw [Nat.mod_eq_of_lt hS] at h
  have h' : (16 * oddSum S 56 + evenSum S 56 : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- A nibble from its four bits. -/
theorem nib_bits (S i : Nat) :
    nib S i = (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2 := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [Nat.pow_mul]
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [nib, e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem nib_lt (S i : Nat) : nib S i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem mag_lt {n : Nat} (hn : n < 16) : mag n < 9 := by unfold mag; split <;> omega

/-- The affine point `(x, y)` negated: `(-x, y)`. -/
def negAff (q : Fe × Fe) : Fe × Fe := (0 - q.1, q.2)

theorem basePt_neg (q : Fe × Fe) : basePt (negAff q) = negPoint (basePt q) := rfl

/-- The entry for the digit `n - 8` of table `j`, negated for a negative digit, represents
`[(n - 8) 256^j] B`. -/
theorem baseEntry_ok (j n : Nat) (hj : j < 56) (hn : n < 16) :
    Rep (basePt (if n < 8 then negAff (baseTable j (mag n)) else baseTable j (mag n)))
      ((((n : ℤ) - 8) * 256 ^ j) • baseAff) := by
  have hr := baseTable_ok j (mag n) hj (mag_lt hn)
  by_cases hlt : n < 8
  · simp only [hlt, ↓reduceIte, basePt_neg]
    have e : ((n : ℤ) - 8) * 256 ^ j = -(((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : n ≤ 8)]; ring
    rw [e, neg_smul, natCast_zsmul]
    exact hr.neg
  · simp only [hlt, ↓reduceIte]
    have e : ((n : ℤ) - 8) * 256 ^ j = (((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ n)]; ring
    rw [e, natCast_zsmul]
    exact hr

theorem zsmul_16 (v w : ℤ) (P : EPoint dZ) :
    (16 : Nat) • (v • P) + w • P = (16 * v + w) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul]; rfl

end VG.Proof.X448
