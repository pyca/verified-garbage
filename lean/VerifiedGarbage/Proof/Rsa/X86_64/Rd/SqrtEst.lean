module

public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Bignum.SqrtRem
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the square root's arithmetic, apart from its steps' symbolic execution

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root's digit estimate

A digit of the square root by words (`Proof/Bignum/SqrtRem.lean`) is
estimated as the 3-by-2 quotient (`R2Words.quot`, `refine3`) of the
remainder's top three words, halved, by the root's top two: at least the
digit and at most two above it (`est_bounds`), so three corrections find it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG.Spec.Rsa (isqrt)
open VG.Proof.Bignum.SqrtRem

/-- `a² ≤ x` exactly where `a ≤ isqrt x`. -/
theorem sq_le_iff (a x : Nat) : a * a ≤ x ↔ a ≤ isqrt x := by
  have lo := VG.Proof.Rsa.RecoverDet.isqrt_sq_le x
  have hi := VG.Proof.Rsa.RecoverDet.lt_succ_isqrt_sq x
  constructor
  · intro h
    refine Nat.le_of_not_lt fun c => ?_
    have := Nat.mul_le_mul (show isqrt x + 1 ≤ a from c) (show isqrt x + 1 ≤ a from c)
    omega
  · intro h
    exact Nat.le_trans (Nat.mul_le_mul h h) lo

/-- `(s β + t)² = s² β² + (2 s β + t) t`. -/
theorem sq_split (s t β : Nat) : (s * β + t) * (s * β + t) = s * s * (β * β) + (2 * s * β + t) * t := by
  grind

/-- The digit after the root `s` (remainder `r`) of `A = s² + r` for the next
pair `P`: `isqrt (A β² + P) - s β`; a `t` fits, `(2 s β + t) t ≤ r β² + P`,
exactly where `t` is at most it. -/
theorem fits_iff {s r P β : Nat} (t : Nat) :
    (2 * s * β + t) * t ≤ r * (β * β) + P ↔ t ≤ isqrt ((s * s + r) * (β * β) + P) - s * β ∧
      s * β ≤ isqrt ((s * s + r) * (β * β) + P) := by
  have e : (s * s + r) * (β * β) + P = s * s * (β * β) + (r * (β * β) + P) := by
    rw [Nat.add_mul]; omega
  have hsb : s * β ≤ isqrt ((s * s + r) * (β * β) + P) := by
    rw [← sq_le_iff, e, show s * β * (s * β) = s * s * (β * β) by grind]; omega
  rw [e] at hsb ⊢
  have := (sq_le_iff (s * β + t) (s * s * (β * β) + (r * (β * β) + P)))
  rw [sq_split] at this
  constructor
  · intro h; exact ⟨by have := this.mp (by omega); omega, hsb⟩
  · intro ⟨h, _⟩; have := this.mpr (by omega); omega

/-- The digit is a digit (`IsDigit`). -/
theorem isDigit_dig (s r P β : Nat) :
    IsDigit β s (r * (β * β) + P) (isqrt ((s * s + r) * (β * β) + P) - s * β) := by
  refine ⟨(fits_iff _).mpr ⟨Nat.le_refl _, (fits_iff 0).mp (by simp) |>.2⟩, ?_⟩
  refine Nat.lt_of_not_le fun h => ?_
  have := ((fits_iff _).mp h).1
  omega

/-- A truncated quotient: dividing both `A` and `Bv` by `P` first, where the
truncated divisor is at least `2^64` and the quotient below `2^64 + 1`, gives
the quotient or one more. -/
theorem trunc_div {β A Bv P : Nat} (hP : 0 < P) (hD : β ≤ Bv / P) (hβ : 1 ≤ β)
    (hU : A / P < (β + 1) * (Bv / P)) :
    A / Bv ≤ A / P / (Bv / P) ∧ A / P / (Bv / P) ≤ A / Bv + 1 := by
  have hD0 : 0 < Bv / P := by omega
  have hB0 : 0 < Bv := by
    rcases Nat.eq_zero_or_pos Bv with h | h
    · rw [h, Nat.zero_div] at hD; omega
    · exact h
  have hdp : Bv / P * P ≤ Bv := Nat.div_mul_le_self Bv P
  have hdp' : Bv < (Bv / P + 1) * P := by
    have := Nat.lt_div_mul_add (a := Bv) hP
    rw [Nat.add_mul, Nat.one_mul]; exact this
  generalize hQ : A / Bv = Q
  have hQ1 : Q * Bv ≤ A := by rw [← hQ]; exact Nat.div_mul_le_self A Bv
  have hQ2 : A < (Q + 1) * Bv := by
    have := Nat.lt_div_mul_add (a := A) hB0; rw [hQ] at this; rw [Nat.add_mul, Nat.one_mul]; exact this
  generalize hD' : Bv / P = D at hD hD0 hdp hdp' hU
  generalize hU' : A / P = U at hU
  have hUP : U * P ≤ A := by rw [← hU']; exact Nat.div_mul_le_self A P
  have hUP' : A < (U + 1) * P := by
    have := Nat.lt_div_mul_add (a := A) hP
    rw [hU'] at this; rw [Nat.add_mul, Nat.one_mul]; exact this
  constructor
  · rw [Nat.le_div_iff_mul_le hD0]
    refine Nat.le_of_lt_succ ?_
    have : Q * D * P < (U + 1) * P := by
      calc Q * D * P = Q * (D * P) := Nat.mul_assoc _ _ _
        _ ≤ Q * Bv := Nat.mul_le_mul_left _ hdp
        _ ≤ A := hQ1
        _ < (U + 1) * P := hUP'
    exact Nat.lt_of_mul_lt_mul_right this
  · refine Nat.le_of_not_lt fun c => ?_
    generalize ht : U / D = t at c
    have ht1 : t * D ≤ U := by rw [← ht]; exact Nat.div_mul_le_self U D
    have htb : t ≤ β := by
      have : U / D < β + 1 := (Nat.div_lt_iff_lt_mul hD0).mpr hU
      omega
    -- `t Bv < t (D + 1) P = t D P + t P ≤ A + t P < (Q + 1) Bv + t P`.
    have h1 : t * Bv < t * ((D + 1) * P) := Nat.mul_lt_mul_of_pos_left hdp' (by omega)
    have h2 : t * ((D + 1) * P) = t * D * P + t * P := by grind
    have h3 : t * D * P ≤ A := Nat.le_trans (Nat.mul_le_mul_right _ ht1) hUP
    have h4 : (Q + 2) * Bv ≤ t * Bv := Nat.mul_le_mul_right _ (by omega)
    have h5 : t * P ≤ β * P := Nat.mul_le_mul_right _ htb
    have h6 : β * P ≤ D * P := Nat.mul_le_mul_right _ hD
    have h7 : (Q + 2) * Bv = (Q + 1) * Bv + Bv := by grind
    omega

theorem pow128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide

/-- A 3-by-2 quotient is at most the 2-by-1 one of its top words. -/
theorem div_le_div21 {U D a d1 β : Nat} (hd1 : 0 < d1) (hU : U < (a + 1) * β) (hD : d1 * β ≤ D) :
    U / D ≤ a / d1 := by
  rw [Nat.le_div_iff_mul_le hd1]
  have h1 : U / D * D ≤ U := Nat.div_mul_le_self U D
  have h2 : U / D * (d1 * β) ≤ U / D * D := Nat.mul_le_mul_left _ hD
  have h3 : U / D * d1 * β < (a + 1) * β := by rw [Nat.mul_assoc]; omega
  have := Nat.lt_of_mul_lt_mul_right h3
  omega

/-- The 2-by-1 estimate from `u₂ u₁` by `d₁` is the 3-by-2 one (capped at
`2^64 - 1`) or at most two more, for `d₁ ≥ 2^63`. -/
theorem est21 {u2 u1 u0 d1 d0 : Nat} (hu0 : u0 < 2 ^ 64) (hd0 : d0 < 2 ^ 64)
    (hd : 2 ^ 63 ≤ d1) :
    min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) ≤
        min ((u2 * 2 ^ 64 + u1) / d1) (2 ^ 64 - 1) ∧
      min ((u2 * 2 ^ 64 + u1) / d1) (2 ^ 64 - 1) ≤
        min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) + 2 := by
  have hd1 : 0 < d1 := by omega
  have hD0 : 0 < d1 * 2 ^ 64 + d0 := by omega
  have ge : (u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0) ≤ (u2 * 2 ^ 64 + u1) / d1 :=
    div_le_div21 (β := 2 ^ 64) hd1 (by rw [pow128]; omega) (by omega)
  by_cases hlt : u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 < d1 * 2 ^ 128 + d0 * 2 ^ 64 + 0
  · have e2 : 64 * (3 - 1) = 128 := rfl
    have e1 : 64 * (3 - 2) = 64 := rfl
    have e0 : 64 * (3 - 3) = 0 := rfl
    obtain ⟨-, a, b, -, -⟩ := VG.Proof.Bignum.X86_64.R2w.norm3 (w := 3) (Xl := 0) (ml := 0)
      (X := u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) (M := d1 * 2 ^ 128 + d0 * 2 ^ 64 + 0)
      (u2 := u2) (u1 := u1) (u0 := u0) (d1 := d1) (d0 := d0) (Nat.le_refl 3)
      (by rw [e2, e1, e0, Nat.pow_zero, Nat.mul_one, Nat.add_zero]) (by rw [e0, Nat.pow_zero]; exact Nat.one_pos)
      (by rw [e2, e1]) (by rw [e1]; exact Nat.two_pow_pos 64) hu0 hd0 hd hlt
    exact ⟨a, b⟩
  · -- `U ≥ D 2^64`: both are capped.
    have hq : 2 ^ 64 ≤ (u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0) := by
      rw [Nat.le_div_iff_mul_le hD0]
      rw [pow128] at hlt ⊢
      omega
    rw [Nat.min_eq_right (show 2 ^ 64 - 1 ≤ (u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0) by omega),
      Nat.min_eq_right (show 2 ^ 64 - 1 ≤ (u2 * 2 ^ 64 + u1) / d1 by omega)]
    omega

/-- The truncations of a digit step, at step `k + 1` (the root `s` of `k + 1`
words of `β = 2 H`, its top word normalized; `r ≤ 2 s`; the next pair `P`),
for `Pk = β^k` (`1`, or at least `β`): for `R = r β² + P`, `U = ⌊R / 2⌋ / Pk`
and `D = s β / Pk`, `D`'s top word is `s / Pk` and at least `H`, `U`'s top
word at most it, `U < (β + 1) D`, and the capped quotient `min (U / D) (β - 1)`
is the digit or at most two more. -/
theorem est_bounds {β H Pk s r P : Nat} (hH : 2 * H = β) (h4 : 4 ≤ β) (hK : 0 < Pk) (hK1 : Pk = 1 ∨ β ≤ Pk)
    (hs : H * Pk ≤ s) (hs' : s < β * Pk) (hr : r ≤ 2 * s) (hP : P < β * β) :
    H * β ≤ s * β / Pk ∧ s * β / Pk < β * β ∧ s * β / Pk / β = s / Pk ∧
      (r * (β * β) + P) / 2 / Pk / (β * β) ≤ s / Pk ∧
      (r * (β * β) + P) / 2 / Pk < (β + 1) * (s * β / Pk) ∧
      isqrt ((s * s + r) * (β * β) + P) - s * β ≤ min ((r * (β * β) + P) / 2 / Pk / (s * β / Pk)) (β - 1) ∧
      min ((r * (β * β) + P) / 2 / Pk / (s * β / Pk)) (β - 1) ≤ isqrt ((s * s + r) * (β * β) + P) - s * β + 2 := by
  have hβ0 : 0 < β := by omega
  obtain ⟨lo, hi⟩ := isDigit_dig s r P β
  have hqβ : isqrt ((s * s + r) * (β * β) + P) - s * β < β := digit_lt hr hP lo
  generalize isqrt ((s * s + r) * (β * β) + P) - s * β = q at lo hi hqβ ⊢
  generalize hR : r * (β * β) + P = R at lo hi ⊢
  have hs0 : 0 < s := by
    have : 0 < H * Pk := Nat.mul_pos (by omega) hK
    omega
  -- `D`'s bounds and top word.
  have hDlo : H * β ≤ s * β / Pk := by
    rw [Nat.le_div_iff_mul_le hK]
    calc H * β * Pk = H * Pk * β := Nat.mul_right_comm _ _ _
      _ ≤ s * β := Nat.mul_le_mul_right _ hs
  have hDhi : s * β / Pk < β * β := by
    rw [Nat.div_lt_iff_lt_mul hK]
    calc s * β < β * Pk * β := Nat.mul_lt_mul_of_pos_right hs' hβ0
      _ = β * β * Pk := Nat.mul_right_comm _ _ _
  have hd1 : s * β / Pk / β = s / Pk := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm Pk, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hβ0]
  -- `R + 1 ≤ 2 s β² + β²`.
  have hRle : R + 1 ≤ 2 * s * (β * β) + β * β := by
    rw [← hR]; have := Nat.mul_le_mul_right (β * β) hr; omega
  have hR2 : R / 2 * 2 ≤ R := Nat.div_mul_le_self R 2
  -- `U`'s top word at most `D`'s.
  have hu2 : R / 2 / Pk / (β * β) ≤ s / Pk := by
    have hs1 : s < (s / Pk + 1) * Pk := by
      have := Nat.lt_div_mul_add (a := s) hK; rw [Nat.add_mul, Nat.one_mul]; exact this
    have hX : R / 2 / Pk * Pk ≤ R / 2 := Nat.div_mul_le_self _ _
    have m1 := Nat.mul_le_mul_right (β * β) (show s + 1 ≤ (s / Pk + 1) * Pk from hs1)
    have e1 : (s + 1) * (β * β) = s * (β * β) + β * β := by grind
    have e3 : 2 * s * (β * β) = 2 * (s * (β * β)) := by grind
    rw [e1] at m1; rw [e3] at hRle
    have h1 : R / 2 / Pk * Pk < (s / Pk + 1) * (β * β) * Pk := by
      rw [Nat.mul_right_comm]; omega
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hβ0 hβ0)).mpr h2)
  -- `U < (β + 1) D`.
  have hUD : R / 2 / Pk < (β + 1) * (s * β / Pk) := by
    rcases hK1 with hk1 | hk
    · -- `Pk = 1`: no truncation.
      subst hk1
      rw [Nat.div_one, Nat.div_one]
      rw [Nat.mul_one] at hs
      have e : (β + 1) * (s * β) = s * (β * β) + s * β := by grind
      have e3 : 2 * s * (β * β) = 2 * (s * (β * β)) := by grind
      have : H * β ≤ s * β := Nat.mul_le_mul_right _ hs
      have e4 : 2 * (H * β) = β * β := by rw [← Nat.mul_assoc, hH]
      rw [e]; rw [e3] at hRle
      omega
    · -- `Pk ≥ β`: `2 U Pk ≤ 2 s β² + β² - 1 < 2 (β D Pk + β Pk) + β² ≤ 2 (β + 1) D Pk`.
      have hU1 : R / 2 / Pk * Pk ≤ R / 2 := Nat.div_mul_le_self _ _
      have hD1 : s * β < (s * β / Pk + 1) * Pk := by
        have := Nat.lt_div_mul_add (a := s * β) hK; rw [Nat.add_mul, Nat.one_mul]; exact this
      generalize s * β / Pk = D at hDlo hD1 ⊢
      generalize R / 2 / Pk = U at hU1 ⊢
      refine Nat.lt_of_mul_lt_mul_right (a := Pk) ?_
      have h3 : β * (s * β) < β * ((D + 1) * Pk) := Nat.mul_lt_mul_of_pos_left hD1 hβ0
      have h4' : H * β * Pk ≤ D * Pk := Nat.mul_le_mul_right _ hDlo
      have f1 : β * (s * β) = s * (β * β) := by grind
      have f2 : β * ((D + 1) * Pk) = β * (D * Pk) + β * Pk := by grind
      have f3 : (β + 1) * D * Pk = β * (D * Pk) + D * Pk := by grind
      have f4 : 2 * s * (β * β) = 2 * (s * (β * β)) := by grind
      -- `D Pk ≥ H β Pk ≥ β Pk + β² / 2` as `H ≥ 2` and `Pk ≥ β`.
      have f5 : 2 * (H * β * Pk) = β * β * Pk := by rw [← Nat.mul_assoc 2, ← Nat.mul_assoc 2, hH]
      have f6 : β * β * β ≤ β * β * Pk := Nat.mul_le_mul_left _ hk
      have f7 : 4 * (β * β) ≤ β * β * β := by
        have := Nat.mul_le_mul_right (β * β) h4; rw [show β * (β * β) = β * β * β by grind] at this; exact this
      have f8 : 4 * (β * Pk) ≤ β * β * Pk := by
        have := Nat.mul_le_mul_right (β * Pk) h4; rw [show β * (β * Pk) = β * β * Pk by grind] at this; exact this
      rw [f3]
      rw [f1, f2] at h3
      rw [f4] at hRle
      omega
  refine ⟨hDlo, hDhi, hd1, hu2, hUD, ?_, ?_⟩
  · -- The digit is at most the truncated quotient, and below `β`.
    have hd0 : 0 < 2 * s * β := Nat.mul_pos (Nat.mul_pos (by decide) hs0) hβ0
    have h1 := digit_le_div hd0 lo
    rw [show 2 * s * β = 2 * (s * β) by grind, ← Nat.div_div_eq_div_mul] at h1
    have ⟨t1, _⟩ := trunc_div (β := β) (A := R / 2) (Bv := s * β) hK (by
      have : β ≤ H * β := Nat.le_mul_of_pos_left β (show 0 < H by omega)
      omega) (by omega) hUD
    exact Nat.le_min.mpr ⟨Nat.le_trans h1 t1, by omega⟩
  · have hβs : β ≤ 2 * s := by
      have : H ≤ H * Pk := Nat.le_mul_of_pos_right H hK
      omega
    have hd0 : 0 < 2 * s * β := Nat.mul_pos (Nat.mul_pos (by decide) hs0) hβ0
    have h1 := div_le_digit_succ hβs hd0 hqβ hi
    rw [show 2 * s * β = 2 * (s * β) by grind, ← Nat.div_div_eq_div_mul] at h1
    have ⟨_, t2⟩ := trunc_div (β := β) (A := R / 2) (Bv := s * β) hK (by
      have : β ≤ H * β := Nat.le_mul_of_pos_left β (show 0 < H by omega)
      omega) (by omega) hUD
    exact Nat.le_trans (Nat.min_le_left _ _) (by omega)

/-! ## The corrections -/

/-- A multiple of `M ≥ 0`: `0`, `M`, at least `2 M`, or at most `-M`. -/
theorem mul_cases (M z : Int) (hM : 0 ≤ M) : M * z = 0 ∨ M * z = M ∨ 2 * M ≤ M * z ∨ M * z ≤ -M := by
  rcases Int.lt_trichotomy z 0 with h | h | h
  · right; right; right
    have : M * z ≤ M * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) hM
    simpa using this
  · left; rw [h, Int.mul_zero]
  · rcases Int.lt_or_le z 2 with h2 | h2
    · right; left; rw [show z = 1 by omega, Int.mul_one]
    · right; right; left
      have : M * 2 ≤ M * z := Int.mul_le_mul_of_nonneg_left h2 hM
      rw [Int.mul_comm] at this; exact this

/-- Before a correction: the candidate digit `t`, at most two above the digit
`q`, the window `w ≡ R - (Y + t) t` modulo `M`, and `E`'s low two words
`(y₁ β + 2 t - 1) mod β²` (`Y = Y_top + y₁ β`). -/
def FixInv (β M Y R q y1 : Nat) (w e t : Nat) : Prop :=
  q ≤ t ∧ t ≤ q + 2 ∧ t < β ∧ w < M ∧ (∃ z : Int, (w : Int) = (R : Int) - (((Y + t) * t : Nat) : Int) + (M : Int) * z) ∧
    e = (y1 * β + 2 * t + β * β - 1) % (β * β)

/-- A correction keeps `FixInv`: where the window's top bit is set (`M ≤ 2 w`,
so `t > q`), `w + E` and `t - 1`. -/
theorem fix_inv {β M Y Ytop R q y1 w e t w' e' : Nat} {c' : Bool}
    (hY : Y = Ytop + y1 * β) (hy1 : y1 + 2 ≤ β) (hq : q < β)
    (lo : (Y + q) * q ≤ R) (hi : R < (Y + (q + 1)) * (q + 1)) (hR : 2 * R < M)
    (hB : 2 * ((Y + (q + 2)) * (q + 2)) < M)
    (hI : FixInv β M Y R q y1 w e t)
    (hw' : w' + M * c'.toNat = (if M ≤ 2 * w then Ytop + e else 0) + w) (hw'M : w' < M)
    (he' : e' = (e + β * β - 2 * (decide (M ≤ 2 * w)).toNat) % (β * β)) :
    FixInv β M Y R q y1 w' e' (if M ≤ 2 * w then t - 1 else t) := by
  obtain ⟨ht1, ht2, htβ, hwM, ⟨z, hz⟩, he⟩ := hI
  -- The products at `q`, `q + 1` and `q + 2`.
  have p1 : (Y + (q + 1)) * (q + 1) = (Y + q) * q + (Y + 2 * q + 1) := by grind
  have p2 : (Y + (q + 2)) * (q + 2) = (Y + (q + 1)) * (q + 1) + (Y + 2 * q + 3) := by grind
  have hββ : y1 * β + 2 * β ≤ β * β := by have := Nat.mul_le_mul_right β hy1; grind
  -- `t` is `q`, `q + 1` or `q + 2`.
  generalize hP0 : (Y + q) * q = P0 at lo p1
  generalize hP1 : (Y + (q + 1)) * (q + 1) = P1 at hi p1 p2
  generalize hP2 : (Y + (q + 2)) * (q + 2) = P2 at hB p2
  have cases : t = q ∨ t = q + 1 ∨ t = q + 2 := by omega
  rcases cases with rfl | rfl | rfl
  · -- No correction: `T ≥ 0`, so `w = T < M / 2`.
    rw [hP0] at hz
    have hz0 : (M : Int) * z = 0 := by
      rcases mul_cases M z (by omega) with h | h | h | h <;> omega
    have hneg : ¬ M ≤ 2 * w := by omega
    simp only [hneg, ↓reduceIte, Nat.zero_add, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero] at hw' he' ⊢
    have hc : c' = false := by cases c' <;> simp at hw' ⊢ <;> omega
    subst hc
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hw'
    subst hw'
    refine ⟨ht1, ht2, htβ, hwM, ⟨z, by rw [hP0]; exact hz⟩, ?_⟩
    rw [he', he, Nat.add_mod_right, Nat.mod_mod]
  · -- `T(q + 1) < 0`: a correction to `q`.
    rw [hP1] at hz
    have hz1 : (M : Int) * z = M := by
      rcases mul_cases M z (by omega) with h | h | h | h <;> omega
    have hneg : M ≤ 2 * w := by omega
    simp only [hneg, ↓reduceIte, decide_true, Bool.toNat_true, Nat.mul_one, Nat.add_sub_cancel] at hw' he' ⊢
    have he0 : e = y1 * β + 2 * (q + 1) - 1 := by
      rw [he, show y1 * β + 2 * (q + 1) + β * β - 1 = (y1 * β + 2 * (q + 1) - 1) + β * β by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [he0] at hw' he'
    refine ⟨Nat.le_refl _, by omega, by omega, hw'M, ⟨z - c'.toNat, ?_⟩, ?_⟩
    · rw [hP0]
      have hw'' : (w' : Int) + M * c'.toNat = Ytop + (y1 * β + 2 * q + 1 : Nat) + w := by
        rw [show y1 * β + 2 * (q + 1) - 1 = y1 * β + 2 * q + 1 by omega] at hw'
        exact_mod_cast hw'
      rw [hY] at p1
      rw [Int.mul_sub]
      push_cast at p1
      omega
    · rw [he']; congr 1; omega
  · -- `T(q + 2) < 0`: a correction to `q + 1`.
    rw [hP2] at hz
    have hz1 : (M : Int) * z = M := by
      rcases mul_cases M z (by omega) with h | h | h | h <;> omega
    have hneg : M ≤ 2 * w := by omega
    simp only [hneg, ↓reduceIte, decide_true, Bool.toNat_true, Nat.mul_one] at hw' he' ⊢
    rw [show q + 2 - 1 = q + 1 by omega]
    have he0 : e = y1 * β + 2 * (q + 2) - 1 := by
      rw [he, show y1 * β + 2 * (q + 2) + β * β - 1 = (y1 * β + 2 * (q + 2) - 1) + β * β by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [he0] at hw' he'
    refine ⟨by omega, by omega, by omega, hw'M, ⟨z - c'.toNat, ?_⟩, ?_⟩
    · rw [hP1]
      have hw'' : (w' : Int) + M * c'.toNat = Ytop + (y1 * β + 2 * q + 3 : Nat) + w := by
        rw [show y1 * β + 2 * (q + 2) - 1 = y1 * β + 2 * q + 3 by omega] at hw'
        exact_mod_cast hw'
      rw [hY] at p2
      rw [Int.mul_sub]
      push_cast at p2
      omega
    · rw [he']; congr 1; omega

/-- The window's top bit is set exactly where the candidate is above the digit. -/
theorem fix_neg {β M Y R q y1 w e t : Nat}
    (lo : (Y + q) * q ≤ R) (hi : R < (Y + (q + 1)) * (q + 1)) (hR : 2 * R < M)
    (hB : 2 * ((Y + (q + 2)) * (q + 2)) < M) (hI : FixInv β M Y R q y1 w e t) : (M ≤ 2 * w ↔ q < t) := by
  obtain ⟨ht1, ht2, -, hwM, ⟨z, hz⟩, -⟩ := hI
  have p1 : (Y + (q + 1)) * (q + 1) = (Y + q) * q + (Y + 2 * q + 1) := by grind
  have p2 : (Y + (q + 2)) * (q + 2) = (Y + (q + 1)) * (q + 1) + (Y + 2 * q + 3) := by grind
  generalize hP0 : (Y + q) * q = P0 at lo p1
  generalize hP1 : (Y + (q + 1)) * (q + 1) = P1 at hi p1 p2
  generalize hP2 : (Y + (q + 2)) * (q + 2) = P2 at hB p2
  have cases : t = q ∨ t = q + 1 ∨ t = q + 2 := by omega
  rcases cases with rfl | rfl | rfl
  · rw [hP0] at hz
    rcases mul_cases M z (by omega) with h | h | h | h <;> omega
  · rw [hP1] at hz
    rcases mul_cases M z (by omega) with h | h | h | h <;> omega
  · rw [hP2] at hz
    rcases mul_cases M z (by omega) with h | h | h | h <;> omega

/-- At the digit: the window is the remainder `R - (Y + q) q`, and `E + 1` is
`y₁ β + 2 q`. -/
theorem fix_final {β M Y R q y1 w e : Nat} (hy1 : y1 + 2 ≤ β) (lo : (Y + q) * q ≤ R) (hR : 2 * R < M)
    (hI : FixInv β M Y R q y1 w e q) : w = R - (Y + q) * q ∧ (e + 1) % (β * β) = y1 * β + 2 * q := by
  obtain ⟨-, -, hqβ, hwM, ⟨z, hz⟩, he⟩ := hI
  have hββ : y1 * β + 2 * β ≤ β * β := by have := Nat.mul_le_mul_right β hy1; grind
  generalize hP0 : (Y + q) * q = P0 at lo hz ⊢
  have hMz : (M : Int) * z = 0 := by
    rcases mul_cases M z (by omega) with h | h | h | h
    · exact h
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
  refine ⟨by omega, ?_⟩
  have hX : y1 * β + 2 * q < β * β := by omega
  rw [he]
  generalize y1 * β + 2 * q = X at hX ⊢
  generalize β * β = BB at hX ⊢
  rcases Nat.eq_zero_or_pos X with h0 | h0
  · subst h0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show BB - 1 < BB by omega), Nat.sub_add_cancel (show 1 ≤ BB by omega),
      Nat.mod_self]
  · rw [show X + BB - 1 = (X - 1) + BB by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show X - 1 < BB by omega),
      Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hX]

/-- A digit step's numbers, generic over the word `β`: `A = s² + r` (`A`'s
root `s`), the next pair `P`, the window `R = r β² + P`, `D = 2 s β`, and
the estimate's operands `N = R / 2 / P_k` and `D' = s β / P_k`; the digit
`q` and the bounds that the estimate and its corrections need. -/
theorem step_arith {β H Pk s r P A R Y N Dd q : Nat} (hH : 2 * H = β) (h8 : 8 ≤ β) (hK : 0 < Pk)
    (hK1 : Pk = 1 ∨ β ≤ Pk) (hs : H * Pk ≤ s) (hs' : s < β * Pk) (hr : r ≤ 2 * s) (hP : P < β * β)
    (hA : s * s + r = A) (hR : r * (β * β) + P = R) (hY : 2 * s * β = Y) (hN : R / 2 / Pk = N)
    (hD : s * β / Pk = Dd) (hq : isqrt (A * (β * β) + P) - s * β = q) :
    N < β * β * β ∧ H ≤ Dd / β ∧ Dd < β * β ∧ Dd / β = s / Pk ∧ N / (β * β) ≤ Dd / β ∧
      N < (β + 1) * Dd ∧ q ≤ min (N / Dd) (β - 1) ∧ min (N / Dd) (β - 1) ≤ q + 2 ∧
      (Y + q) * q ≤ R ∧ R < (Y + (q + 1)) * (q + 1) ∧ q < β ∧
      2 * ((Y + (q + 2)) * (q + 2)) < β * β * (β * β) * Pk ∧
      isqrt (A * (β * β) + P) = s * β + q ∧ A * (β * β) + P - (s * β + q) * (s * β + q) = R - (Y + q) * q := by
  obtain ⟨eDlo, eDhi, ed1, eu2, eUD, est1, est2⟩ := est_bounds hH (by omega) hK hK1 hs hs' hr hP
  have hdig := isDigit_dig s r P β
  subst hA hR hY hN hD hq
  have hqβ := digit_lt hr hP hdig.1
  obtain ⟨st1, st2⟩ := step_inv (A := s * s + r) rfl hdig
  have hsq := sqrt_of_rem st1 st2
  generalize isqrt ((s * s + r) * (β * β) + P) - s * β = q at *
  have hβ0 : 0 < β := by omega
  have hsK : s / Pk < β := (Nat.div_lt_iff_lt_mul hK).mpr hs'
  refine ⟨?_, (Nat.le_div_iff_mul_le hβ0).mpr eDlo, eDhi, ed1, by rw [ed1]; exact eu2, eUD, est1, est2,
    hdig.1, hdig.2, hqβ, ?_, hsq, by omega⟩
  · have : (r * (β * β) + P) / 2 / Pk / (β * β) < β := by omega
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hβ0 hβ0)] at this
    have e1 : β * β * β = β * (β * β) := Nat.mul_assoc _ _ _
    have e2 : β * β * β = β * β * β := rfl
    have e3 : (β * β) * β = β * (β * β) := Nat.mul_comm _ _
    omega
  · -- `(2 s β + q + 2) (q + 2) < 2 (β P_k) β (β + 1)`, and `4 β + 4 ≤ β²`.
    generalize hT : β * Pk = T at hs'
    have e1 : 2 * s * β + (q + 2) < 2 * T * β := by
      have : (s + 1) * β ≤ T * β := Nat.mul_le_mul_right _ hs'
      rw [Nat.add_mul, Nat.one_mul] at this
      have : 2 * s * β = 2 * (s * β) := Nat.mul_assoc _ _ _
      have : 2 * T * β = 2 * (T * β) := Nat.mul_assoc _ _ _
      omega
    have e2 : (2 * s * β + (q + 2)) * (q + 2) ≤ 2 * T * β * (β + 1) :=
      Nat.mul_le_mul (Nat.le_of_lt e1) (by omega)
    have k1 : 4 * β + 4 < β * β := by
      have := Nat.mul_le_mul_right β h8
      omega
    have k2 : T * β * (4 * β + 4) < T * β * (β * β) :=
      Nat.mul_lt_mul_of_pos_left k1 (Nat.mul_pos (by omega) hβ0)
    have e3 : β * β * (β * β) * Pk = T * β * (β * β) := by rw [← hT]; grind
    have e4 : 2 * (2 * T * β * (β + 1)) = T * β * (4 * β + 4) := by grind
    omega

end VG.Proof.Rsa.X86_64.Rd
