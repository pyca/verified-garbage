module
-- separate module: the square root by words' pieces, for `RdSqrt.lean`'s `sqrt_ok`

public import VerifiedGarbage.Proof.Bignum.SqrtRem
public import VerifiedGarbage.Proof.Bignum.WordStepNorm
public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdShift
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the square root by words

The pieces of `RecoverDet.sqrt`: the estimate of a digit (`est_bounds`), …
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RdSqrtW

open VG.Proof.Bignum.SqrtRem (IsDigit digit_exists digit_lt digit_le_div div_le_digit_succ)

/-! ## The estimate of a digit -/

/-- `⌊a / 2^K⌋ ⌊b⌋`-style truncation: `⌊M / N⌋ ⌊⌋`, the quotient of truncated numbers is at least
that of the numbers' cut, `b ⌊M / N⌋ ≤ ⌊b M / N⌋`. -/
theorem mul_div_le (b M N : Nat) : b * (M / N) ≤ b * M / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  exact (Nat.le_div_iff_mul_le hN).mpr (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))

/-- The estimate's bounds over abstract numbers: a dividend `Y`, a divisor `M` normalized at
`2^(K + 64)`, the digit `q` within one below `⌊Y / M⌋`, and `Y < M β + β² / 2`. -/
theorem est_core {Y M K q : Nat} (hdM : 2 ^ 63 ≤ M * 2 ^ 64 / 2 ^ (K + 64) / 2 ^ 64)
    (sK : 2 ^ 63 * 2 ^ K * 2 ^ 64 ≤ M) (q1 : q ≤ Y / M) (q2 : Y / M ≤ q + 1) (qlt : q < 2 ^ 64)
    (hY : Y + 2 ^ 127 ≤ M * 2 ^ 64 + 2 ^ 127 + 2 ^ 127 - 1) :
    Y / 2 ^ K < (2 ^ 64 + 1) * (M / 2 ^ K) ∧
    min (Y / 2 ^ K / (M / 2 ^ K)) (2 ^ 64 - 1) ≤ min (Y / 2 ^ K / 2 ^ 64 / (M / 2 ^ K / 2 ^ 64)) (2 ^ 64 - 1) ∧
    min (Y / 2 ^ K / 2 ^ 64 / (M / 2 ^ K / 2 ^ 64)) (2 ^ 64 - 1) ≤ min (Y / 2 ^ K / (M / 2 ^ K)) (2 ^ 64 - 1) + 2 ∧
    q ≤ min (Y / 2 ^ K / (M / 2 ^ K)) (2 ^ 64 - 1) ∧ min (Y / 2 ^ K / (M / 2 ^ K)) (2 ^ 64 - 1) ≤ q + 2 := by
  have cut : ∀ a, a * 2 ^ 64 / 2 ^ (K + 64) = a / 2 ^ K := fun a => by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64)]
  by_cases hYM : Y < M * 2 ^ 64
  · obtain ⟨a1, a2, a3, a4, a5⟩ := VG.Proof.Bignum.WordStep.qhat3_div (Y := Y) (M := M) (P := 2 ^ 64)
      (K := K) (Nat.two_pow_pos 64) hYM hdM
    rw [cut, cut] at a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, by omega_using [q1, a4], by omega_using [q2, a5]⟩
  · -- `Y ≥ M β`: the digit, `Q` and `quot`'s estimate are all `β - 1`.
    have hK := Nat.two_pow_pos K
    have hM0 : 0 < M := Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (by decide) hK) (by decide)) sK
    have hYM' : M * 2 ^ 64 ≤ Y := Nat.le_of_not_lt hYM
    have qβ : 2 ^ 64 ≤ Y / M := (Nat.le_div_iff_mul_le hM0).mpr (by rw [Nat.mul_comm]; exact hYM')
    generalize hk : 2 ^ K = k at hK sK ⊢
    have Dbig : 2 ^ 63 * 2 ^ 64 ≤ M / k := by
      refine (Nat.le_div_iff_mul_le hK).mpr ?_
      rw [show 2 ^ 63 * 2 ^ 64 * k = 2 ^ 63 * k * 2 ^ 64 by rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc]]
      exact sK
    have hD0 : 0 < M / k := by omega_using [Dbig]
    have hD1 : 0 < M / k / 2 ^ 64 :=
      Nat.div_pos (Nat.le_trans (by decide) Dbig) (Nat.two_pow_pos 64)
    have UD : 2 ^ 64 * (M / k) ≤ Y / k :=
      Nat.le_trans (mul_div_le _ _ _) (Nat.div_le_div_right (by rw [Nat.mul_comm]; exact hYM'))
    have Qβ : 2 ^ 64 ≤ Y / k / (M / k) := (Nat.le_div_iff_mul_le hD0).mpr UD
    have mQ : min (Y / k / (M / k)) (2 ^ 64 - 1) = 2 ^ 64 - 1 := Nat.min_eq_right (by omega_arith)
    have mQ2 : min (Y / k / 2 ^ 64 / (M / k / 2 ^ 64)) (2 ^ 64 - 1) = 2 ^ 64 - 1 := by
      refine Nat.min_eq_right (Nat.le_trans (Nat.sub_le _ _) ((Nat.le_div_iff_mul_le hD1).mpr ?_))
      have := Nat.div_le_div_right (c := 2 ^ 64) UD
      rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)] at this
      exact Nat.le_trans (Nat.le_trans (Nat.le_of_eq (Nat.mul_comm _ _)) (Nat.div_mul_le_self _ _)) this
    rw [mQ, mQ2]
    refine ⟨?_, Nat.le_refl _, by omega_using [], by omega_using [qlt], by omega_arith⟩
    -- `U < (β + 1) D`: `D k ≥ M - k + 1` and `Y + (β + 1) (k - 1) < (β + 1) M`.
    have hMk : M + 1 ≤ M / k * k + k := by
      have := VG.Proof.Bignum.WordStep.lt_succ_div_mul M k hK
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
    have h1 := Nat.mul_le_mul_left (2 ^ 64 + 1) hMk
    simp only [Nat.mul_add, Nat.mul_one] at h1
    refine (Nat.div_lt_iff_lt_mul hK).mpr ?_
    rw [Nat.mul_assoc]
    generalize M / k * k = Dk at h1 ⊢
    omega_arith

/-- The estimate of the digit after the root `s` (`j` words, normalized: its top word at least
`2^63`), with the remainder `r ≤ 2 s` and the next two words `P`: for `R = r β² + P`, `U` the top
three words of `⌊R / 2⌋` and `D` the top two of `s β` (cut at `2^(64 (j - 1))`),
`Q = min(⌊U / D⌋, β - 1)` is between the digit `q` and `q + 2`, `quot`'s 2-by-1 estimate from `U`'s
and `D`'s top words is within 2 above `Q`, and `U < (β + 1) D`. -/
theorem est_bounds {j s r P q : Nat} (hs : 2 ^ 63 ≤ s / 2 ^ (64 * (j - 1)))
    (hr : r ≤ 2 * s) (hP : P < 2 ^ 64 * 2 ^ 64)
    (hq : IsDigit (2 ^ 64) s (r * (2 ^ 64 * 2 ^ 64) + P) q) :
    (r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) < (2 ^ 64 + 1) * (s * 2 ^ 64 / 2 ^ (64 * (j - 1))) ∧
    min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / (s * 2 ^ 64 / 2 ^ (64 * (j - 1)))) (2 ^ 64 - 1) ≤
      min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / 2 ^ 64 /
        (s * 2 ^ 64 / 2 ^ (64 * (j - 1)) / 2 ^ 64)) (2 ^ 64 - 1) ∧
    min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / 2 ^ 64 /
        (s * 2 ^ 64 / 2 ^ (64 * (j - 1)) / 2 ^ 64)) (2 ^ 64 - 1) ≤
      min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / (s * 2 ^ 64 / 2 ^ (64 * (j - 1)))) (2 ^ 64 - 1) + 2 ∧
    q ≤ min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / (s * 2 ^ 64 / 2 ^ (64 * (j - 1)))) (2 ^ 64 - 1) ∧
    min ((r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / (s * 2 ^ 64 / 2 ^ (64 * (j - 1)))) (2 ^ 64 - 1) ≤
      q + 2 := by
  obtain ⟨lo, hi⟩ := hq
  have hK := Nat.two_pow_pos (64 * (j - 1))
  have sK : 2 ^ 63 * 2 ^ (64 * (j - 1)) ≤ s :=
    Nat.le_trans (Nat.mul_le_mul_right (2 ^ (64 * (j - 1))) hs) (Nat.div_mul_le_self _ _)
  have hβs : 2 ^ 64 ≤ 2 * s := by
    have := Nat.mul_le_mul_left (2 ^ 63) (Nat.one_le_two_pow (n := 64 * (j - 1))); omega_using [hK, sK]
  have hd0 : 0 < 2 * s * 2 ^ 64 := Nat.mul_pos (by omega_arith) (Nat.two_pow_pos 64)
  have qlt : q < 2 ^ 64 := digit_lt hr hP lo
  have q1 := digit_le_div hd0 lo
  have q2 := div_le_digit_succ hβs hd0 qlt hi
  have eq : ∀ R, R / (2 * s * 2 ^ 64) = R / 2 / (s * 2 ^ 64) := fun R => by
    rw [Nat.div_div_eq_div_mul, Nat.mul_assoc]
  rw [eq] at q1 q2
  have hY : (r * (2 ^ 64 * 2 ^ 64) + P) / 2 + 2 ^ 127 ≤ s * 2 ^ 64 * 2 ^ 64 + 2 ^ 127 + 2 ^ 127 - 1 := by
    have := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ 64) hr
    rw [Nat.mul_assoc s]
    omega_using [hr, hP]
  have hdM : 2 ^ 63 ≤ s * 2 ^ 64 * 2 ^ 64 / 2 ^ (64 * (j - 1) + 64) / 2 ^ 64 := by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64), Nat.div_div_eq_div_mul,
      Nat.mul_comm (2 ^ (64 * (j - 1))), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos 64)]
    exact hs
  exact est_core hdM (Nat.mul_le_mul_right _ sK) q1 q2 qlt hY

/-! ## A step's arithmetic -/

/-- The multiply-and-subtract and two corrections, modulo `M = 2 H`: from `q ≤ Q ≤ q + 2` for the digit `q`
(`(a + q) q ≤ R < (a + q + 1) (q + 1)`), each correction adding `a + 2 Q - 1` and taking one from `Q` where
the window is negative (at least `H`), the last `Q` is `q` and the window `R - (a + q) q`. -/
theorem corr_chain {H a R q Q W1 b1 W2 c2 W3 c3 : Nat} (hR : R < H) (hd : (a + q) * q ≤ R)
    (hd' : R < (a + (q + 1)) * (q + 1)) (hq1 : q ≤ Q) (hq2 : Q ≤ q + 2)
    (hgap : (a + (q + 2)) * (q + 2) ≤ R + H)
    (h1 : W1 + (a + Q) * Q + 2 * H * b1 = R + 2 * H) (hb1 : b1 < 2) (hW1 : W1 < 2 * H)
    (h2 : W2 + 2 * H * c2 = W1 + W1 / H * (a + 2 * Q - 1)) (hc2 : c2 < 2) (hW2 : W2 < 2 * H)
    (h3 : W3 + 2 * H * c3 = W2 + W2 / H * (a + 2 * (Q - W1 / H) - 1)) (hc3 : c3 < 2) (hW3 : W3 < 2 * H) :
    (W1 / H = 1 → 1 ≤ Q) ∧ (W2 / H = 1 → 1 ≤ Q - W1 / H) ∧ Q - W1 / H - W2 / H = q ∧ W3 = R - (a + q) * q := by
  have cs := fun Q (h : 1 ≤ Q) => VG.Proof.Bignum.SqrtRem.correction_step a Q h
  have e1 : (a + (q + 1)) * (q + 1) = (a + q) * q + (a + 2 * (q + 1) - 1) := by
    have := cs (q + 1) (by omega_using []); rw [Nat.add_sub_cancel] at this; exact this
  have e2 : (a + (q + 2)) * (q + 2) = (a + (q + 1)) * (q + 1) + (a + 2 * (q + 2) - 1) := by
    have := cs (q + 2) (by omega_using []); rw [show q + 2 - 1 = q + 1 by omega_using []] at this; exact this
  have hH : 0 < H := by omega_using [hR]
  rcases (show Q = q ∨ Q = q + 1 ∨ Q = q + 2 by omega_using [hq1, hq2]) with rfl | rfl | rfl
  · -- No correction.
    have w1 : W1 = R - (a + Q) * Q := by
      rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
    have n1 : W1 / H = 0 := Nat.div_eq_of_lt (by omega_using [hR, w1])
    rw [n1] at h2 h3 ⊢
    have w2 : W2 = W1 := by rcases (show c2 = 0 ∨ c2 = 1 by omega_using [hc2]) with rfl | rfl <;> simp at h2 <;> omega_arith
    have n2 : W2 / H = 0 := Nat.div_eq_of_lt (by omega_using [hR, h1, hb1, hW1, h2, hc2, hW2, h3, hc3, hW3, hH, hd, hd', hq1, hq2, hgap, e1, e2, w1, n1, w2])
    rw [n2] at h3 ⊢
    have w3 : W3 = W2 := by rcases (show c3 = 0 ∨ c3 = 1 by omega_using [hc3]) with rfl | rfl <;> simp at h3 <;> omega_arith
    refine ⟨by omega_using [], by omega_using [], by omega_using [], by omega_using [hR, h1, hb1, hW1, h2, hc2, hW2, h3, hc3, hW3, hH, hd, hd', hq1, hq2, hgap, e1, e2, w1, n1, w2, n2, w3]⟩
  · -- One correction.
    generalize (a + (q + 2)) * (q + 2) = d2 at hgap e2
    generalize (a + (q + 1)) * (q + 1) = d1 at hd' h1 e1 e2
    generalize (a + q) * q = d0 at hd e1 ⊢
    have w1 : W1 = 2 * H - (d1 - R) := by
      rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
    have n1 : W1 / H = 1 := Nat.div_eq_of_lt_le (by omega_using [hR, hb1, hW1, hc2, hW2, hc3, hW3, hH, hq1, hq2, h2, h3, hgap, hd', h1, e2, hd, e1, w1]) (by omega_using [hW1])
    rw [n1] at h2 h3 ⊢
    rw [Nat.one_mul] at h2
    have w2 : W2 = R - d0 := by
      rcases (show c2 = 0 ∨ c2 = 1 by omega_using [hc2]) with rfl | rfl <;> omega_using [hR, hb1, hW1, hW2, hc3, hW3, hH, hq1, hq2, h3, hgap, hd', h1, e2, hd, e1, w1, n1, h2]
    have n2 : W2 / H = 0 := Nat.div_eq_of_lt (by omega_using [hR, w2])
    rw [n2] at h3 ⊢
    have w3 : W3 = W2 := by rcases (show c3 = 0 ∨ c3 = 1 by omega_using [hc3]) with rfl | rfl <;> simp at h3 <;> omega_arith
    refine ⟨by omega_using [], by omega_using [], by omega_using [], by omega_using [hR, hb1, hW1, hW2, hc3, hW3, hH, hq1, hq2, h2, h3, hgap, hd', h1, e2, hd, e1, w1, n1, w2, n2, w3]⟩
  · -- Two corrections.
    generalize (a + (q + 2)) * (q + 2) = d2 at hgap h1 e2
    generalize (a + (q + 1)) * (q + 1) = d1 at hd' e1 e2
    generalize (a + q) * q = d0 at hd e1 ⊢
    have w1 : W1 = 2 * H - (d2 - R) := by
      rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
    have n1 : W1 / H = 1 := Nat.div_eq_of_lt_le (by omega_using [hgap, w1]) (by omega_using [hW1])
    rw [n1] at h2 h3 ⊢
    rw [Nat.one_mul] at h2
    rw [show q + 2 - 1 = q + 1 by omega_using []] at h3
    have w2 : W2 = 2 * H - (d1 - R) := by
      rcases (show c2 = 0 ∨ c2 = 1 by omega_using [hc2]) with rfl | rfl <;> omega_using [hR, hb1, hW1, hW2, hc3, hW3, hH, hq1, hq2, h3, hgap, h1, hd', e2, hd, e1, w1, n1, h2]
    have n2 : W2 / H = 1 := Nat.div_eq_of_lt_le (by omega_using [hR, hb1, hW1, hc2, hW2, hc3, hW3, hH, hq1, hq2, h2, h3, hgap, h1, hd', e2, hd, e1, w1, n1, w2]) (by omega_using [hW2])
    rw [n2, Nat.one_mul] at h3
    rw [n2]
    have w3 : W3 = R - d0 := by
      rcases (show c3 = 0 ∨ c3 = 1 by omega_using [hc3]) with rfl | rfl <;> omega_using [hR, hb1, hW1, hW2, hW3, hH, hq1, hq2, h2, hgap, h1, hd', e2, hd, e1, w1, n1, w2, n2, h3]
    refine ⟨by omega_using [], by omega_using [], by omega_using [], w3⟩

/-- A step's bounds, for the root `s` of `j ≥ 1` words (its top word `s₀ ≥ 2^63`), `r ≤ 2 s`, the next pair
`P` and its digit `q`, `R = r β² + P` and `H = 2^(64 (j + 3) - 1)`: `R < H`, the corrections' room
`(2 s β + q + 2) (q + 2) ≤ R + H`, and `U = ⌊R / 2⌋ / 2^(64 (j - 1))` has three words, the top one at most
`s₀`. -/
theorem step_bounds {j s r P q : Nat} (hj : 1 ≤ j) (hs' : s < 2 ^ (64 * j)) (hr : r ≤ 2 * s)
    (hP : P < 2 ^ 64 * 2 ^ 64) (hq : q < 2 ^ 64) :
    r * (2 ^ 64 * 2 ^ 64) + P < 2 ^ (64 * (j + 2) + 63) ∧
    (2 * s * 2 ^ 64 + (q + 2)) * (q + 2) ≤ r * (2 ^ 64 * 2 ^ 64) + P + 2 ^ (64 * (j + 2) + 63) ∧
    (r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / (2 ^ 64 * 2 ^ 64) ≤ s / 2 ^ (64 * (j - 1)) ∧
    (r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) < 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
  have eL : 2 ^ (64 * j) = 2 ^ (64 * (j - 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega_using [hj]
  have eH : 2 ^ (64 * (j + 2) + 63) = 2 ^ (64 * (j - 1)) * (2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 63) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hj]
  rw [eL] at hs'
  rw [eH]
  have hK := Nat.two_pow_pos (64 * (j - 1))
  generalize 2 ^ (64 * (j - 1)) = K at hK hs' ⊢
  have hsK := VG.Proof.Bignum.WordStep.lt_succ_div_mul s K hK
  generalize s / K = s0 at hsK ⊢
  have hrs := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ 64) hr
  have hq1 : q + 2 ≤ 2 * 2 ^ 64 := by omega_using [hq]
  have hq2 := Nat.mul_le_mul (Nat.add_le_add_left hq1 (2 * s * 2 ^ 64)) hq1
  have e1 : (2 * s * 2 ^ 64 + 2 * 2 ^ 64) * (2 * 2 ^ 64) = 4 * (s * (2 ^ 64 * 2 ^ 64)) + 4 * (2 ^ 64 * 2 ^ 64) := by
    ring
  rw [e1] at hq2
  -- `s < K β`, as a bound on `s β²`.
  have hsβ := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ 64) (show s + 1 ≤ K * 2 ^ 64 by omega_using [hs'])
  have e4 : (s + 1) * (2 ^ 64 * 2 ^ 64) = s * (2 ^ 64 * 2 ^ 64) + 2 ^ 64 * 2 ^ 64 := by ring
  have e5 : K * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) = K * (2 ^ 64 * 2 ^ 64 * 2 ^ 64) := by ring
  rw [e4, e5] at hsβ
  have e6 : K * (2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 63) = K * (2 ^ 64 * 2 ^ 64 * 2 ^ 64) * 2 ^ 63 := by ring
  rw [e6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega_using [hr, hP, hs']
  · clear e1 e4 e5 e6
    omega_using [hs', hq2]
  · refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide) (by decide))).mpr
      ((Nat.div_lt_iff_lt_mul hK).mpr ?_))
    have h1 := Nat.mul_le_mul_right (2 ^ 64 * 2 ^ 64) (show s + 1 ≤ (s0 + 1) * K by omega_using [hsK])
    have e7 : (s0 + 1) * (2 ^ 64 * 2 ^ 64) * K = (s0 + 1) * K * (2 ^ 64 * 2 ^ 64) := by ring
    rw [Nat.succ_eq_add_one, e7]
    rw [e4] at h1
    omega_using [hr, hP, hsK]
  · rw [Nat.div_lt_iff_lt_mul hK]
    rw [show 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * K = K * (2 ^ 64 * 2 ^ 64 * 2 ^ 64) by ring]
    omega_using [hr, hP, hs']

/-- The first correction's condition: the window is negative only where `Q ≥ 1`. -/
theorem corr1 {H a R Q W1 b1 : Nat} (hR : R < H)
    (h1 : W1 + (a + Q) * Q + 2 * H * b1 = R + 2 * H) (hb1 : b1 < 2) (hW1 : W1 < 2 * H) :
    W1 / H = 1 → 1 ≤ Q := by
  intro hn
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  rw [Nat.mul_zero, Nat.add_zero] at h1
  have : W1 = R := by rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
  rw [this, Nat.div_eq_of_lt hR] at hn
  exact absurd hn (by decide)

/-- The second correction's condition. -/
theorem corr2 {H a R q Q W1 b1 W2 c2 : Nat} (hR : R < H) (hd : (a + q) * q ≤ R)
    (hd' : R < (a + (q + 1)) * (q + 1)) (hq1 : q ≤ Q) (hq2 : Q ≤ q + 2)
    (hgap : (a + (q + 2)) * (q + 2) ≤ R + H)
    (h1 : W1 + (a + Q) * Q + 2 * H * b1 = R + 2 * H) (hb1 : b1 < 2) (hW1 : W1 < 2 * H)
    (h2 : W2 + 2 * H * c2 = W1 + W1 / H * (a + 2 * Q - 1)) (hc2 : c2 < 2) (hW2 : W2 < 2 * H) :
    W2 / H = 1 → 1 ≤ Q - W1 / H := by
  intro hn2
  have hn1 : W1 / H ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega_using [hR])).mpr (by omega_using [hW1]))
  by_cases hQ : 2 ≤ Q
  · omega_using [hn1, hQ]
  have e1 : (a + (q + 1)) * (q + 1) = (a + q) * q + (a + 2 * (q + 1) - 1) := by
    have := VG.Proof.Bignum.SqrtRem.correction_step a (q + 1) (by omega_using [])
    rw [Nat.add_sub_cancel] at this; exact this
  rcases (show Q = q ∨ Q = q + 1 by omega_using [hq1, hQ]) with rfl | rfl
  · have w1 : W1 = R - (a + Q) * Q := by
      rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
    have n1 : W1 / H = 0 := Nat.div_eq_of_lt (by omega_using [hR, w1])
    rw [n1, Nat.zero_mul, Nat.add_zero] at h2
    have w2 : W2 = W1 := by rcases (show c2 = 0 ∨ c2 = 1 by omega_using [hc2]) with rfl | rfl <;> omega_arith
    rw [w2, n1] at hn2
    exact absurd hn2 (by decide)
  · have mono : (a + (q + 1)) * (q + 1) ≤ (a + (q + 2)) * (q + 2) := Nat.mul_le_mul (by omega_using []) (by omega_using [])
    generalize (a + (q + 2)) * (q + 2) = d2 at hgap mono
    generalize (a + (q + 1)) * (q + 1) = d1 at hd' h1 e1 mono
    generalize (a + q) * q = d0 at hd e1
    have w1 : W1 = 2 * H - (d1 - R) := by
      rcases (show b1 = 0 ∨ b1 = 1 by omega_using [hb1]) with rfl | rfl <;> omega_arith
    have n1 : W1 / H = 1 := Nat.div_eq_of_lt_le (by omega_using [hR, hb1, hW1, hc2, hW2, hn2, hn1, hq1, hq2, h2, hQ, hgap, hd', h1, mono, hd, e1, w1]) (by omega_using [hW1])
    rw [n1, Nat.one_mul] at h2
    have w2 : W2 = R - d0 := by
      rcases (show c2 = 0 ∨ c2 = 1 by omega_using [hc2]) with rfl | rfl <;> omega_using [hR, hb1, hW1, hW2, hn2, hn1, hq1, hq2, hQ, hgap, hd', h1, mono, hd, e1, w1, n1, h2]
    rw [w2, Nat.div_eq_of_lt (by omega_using [hR])] at hn2
    exact absurd hn2 (by decide)

/-! ## The first digit, in registers -/

section Digit0
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE

/-- A step of the first digit's loop, in numbers: the next two bits of `X` (`r14`, `r15`) into the
remainder `R` (`r16`, `r17`), and the root `Y` (`r18`) doubled, plus one where `4 Y + 1` fits. -/
theorem digit0Step_ok {s : State} (h20 : s.gpr .r20 = BitVec.ofNat 64 0) (hY : (s.gpr .r18).toNat < 2 ^ 63)
    (hR : (s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r17).toNat ≤ 2 * (s.gpr .r18).toNat) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Step ++ ([.subi .r8 .r8 1] : List Instr))) s fun t =>
      ((t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r15).toNat =
          4 * ((s.gpr .r14).toNat * 2 ^ 64 + (s.gpr .r15).toNat) % 2 ^ 128 ∧
        (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat =
          (if 4 * ((s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r17).toNat) + (s.gpr .r14).toNat / 2 ^ 62 <
              4 * (s.gpr .r18).toNat + 1
            then 4 * ((s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r17).toNat) + (s.gpr .r14).toNat / 2 ^ 62
            else 4 * ((s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r17).toNat) + (s.gpr .r14).toNat / 2 ^ 62 -
              (4 * (s.gpr .r18).toNat + 1)) ∧
        (t.gpr .r18).toNat = (if 4 * ((s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r17).toNat) +
            (s.gpr .r14).toNat / 2 ^ 62 < 4 * (s.gpr .r18).toNat + 1
          then 2 * (s.gpr .r18).toNat else 2 * (s.gpr .r18).toNat + 1) ∧
        t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.gpr .r8 = s.gpr .r8 - BitVec.ofNat 64 1 ∧ t.mem = s.mem) ∧
      Keep [.r0, .r3, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18] s t := by
  refine WP.keep _ ?_ (by decide)
  mcrun [VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Step, h20, exec_lsl (show 2 < 64 by decide),
    exec_lsr_d (show 62 < 64 by decide)]
  generalize s.gpr .r14 = a at hY hR ⊢
  generalize s.gpr .r15 = b at hY hR ⊢
  generalize s.gpr .r16 = rh at hY hR ⊢
  generalize s.gpr .r17 = rl at hY hR ⊢
  generalize s.gpr .r18 = y at hY hR ⊢
  have ha := a.isLt; have hb := b.isLt; have hrl := rl.isLt; have hrh := rh.isLt
  have f := fun (x z : BitVec 64) => VG.Proof.Rsa.PPC64LE.RdShift.funnel_val x z (c := 62) (by decide) (by decide)
  simp only [show 64 - 62 = 2 from rfl] at f
  have fx := f b a; have fr := f rl rh; have fl := f a rl
  have hb2 : (b <<< 2).toNat = 4 * (b.toNat % 2 ^ 62) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_using []
  have ty : (y >>> 62).toNat = y.toNat / 2 ^ 62 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have tl : (y <<< 2 + 1#64).toNat = 4 * (y.toNat % 2 ^ 62) + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (1#64).toNat = 1 from rfl]; omega_using []
  rw [fx, fr, fl, hb2, ty, tl]
  rw [ty, tl] at *
  have yh : y.toNat / 2 ^ 62 ≤ 1 := by omega_using [hY]
  have rh1 : rh.toNat ≤ 1 := by omega_using [hR]
  -- the carries
  generalize hc1 : decide (18446744073709551615 ≤ a.toNat / 2 ^ 62 + 2 ^ 2 * (rl.toNat % 2 ^ 62) +
    (18446744073709551616 - 1 - (4 * (y.toNat % 2 ^ 62) + 1))) = c1
  generalize hc2 : decide (18446744073709551616 ≤ rl.toNat / 2 ^ 62 + 2 ^ 2 * (rh.toNat % 2 ^ 62) +
    (18446744073709551616 - 1 - y.toNat / 2 ^ 62) + c1.toNat) = c2
  have sel : ∀ (x d : BitVec 64) (c : Bool), (x ^^^ (d ^^^ x) &&& 0#64 - BitVec.ofNat 64 ((0#64).toNat + c.toNat)) =
      if c then d else x := by
    intro x d c; cases c
    · simp
    · simp only [Bool.toNat_true, ↓reduceIte]
      rw [show (0#64).toNat + 1 = 1 from rfl, show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl,
        BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm x d, BitVec.xor_assoc, BitVec.xor_self,
        BitVec.xor_zero]
  rw [sel, sel]
  refine ⟨by omega_using [], ?_, ?_⟩
  · cases c1 <;> cases c2 <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, ↓reduceIte, Bool.false_eq_true, BitVec.toNat_ofNat] at hc1 hc2 ⊢ <;> split <;> omega_arith
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl]
    cases c1 <;> cases c2 <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false] at hc1 hc2 ⊢ <;> split <;> omega_arith

/-- Two more bits of `T < 2^128` brought down: the window `x = (T mod 4^k') 4^i` (`k' = 64 - i`) shifted
up by two, its top two bits, and the top `2 (i + 1)` bits. -/
theorem bits_step {T i : Nat} (hi : i < 64) :
    4 * (T % 4 ^ (64 - i) * 4 ^ i) % 2 ^ 128 = T % 4 ^ (64 - (i + 1)) * 4 ^ (i + 1) ∧
    T % 4 ^ (64 - i) * 4 ^ i / 2 ^ 126 = T / 4 ^ (64 - (i + 1)) % 4 ∧
    T / 4 ^ (64 - (i + 1)) = 4 * (T / 4 ^ (64 - i)) + T / 4 ^ (64 - (i + 1)) % 4 := by
  obtain ⟨k, hk⟩ : ∃ k, 64 - (i + 1) = k := ⟨_, rfl⟩
  have hk1 : 64 - i = k + 1 := by omega_using [hi, hk]
  have hki : k + i = 63 := by omega_using [hi, hk]
  rw [hk1, hk]
  have p4 : ∀ n, (4 : Nat) ^ n = 2 ^ (2 * n) := fun n => by rw [Nat.pow_mul]
  have e63 : 4 ^ k * 4 ^ i = 2 ^ 126 := by rw [← Nat.pow_add, hki, p4]
  have e64 : 4 ^ k * 4 ^ (i + 1) = 2 ^ 128 := by rw [← Nat.pow_add, show k + (i + 1) = 64 by omega_using [hi, hk], p4]
  have hp := Nat.pow_pos (n := k) (show 0 < 4 by decide)
  have hpi := Nat.pow_pos (n := i) (show 0 < 4 by decide)
  -- `T mod 4^(k+1) = T mod 4^k + 4^k d`, `d = ⌊T / 4^k⌋ mod 4`.
  have split : T % 4 ^ (k + 1) = T % 4 ^ k + 4 ^ k * (T / 4 ^ k % 4) := by
    rw [Nat.pow_succ, Nat.mod_mul]
  have lo : T % 4 ^ k * 4 ^ i < 2 ^ 126 := by
    rw [← e63]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hp) hpi
  have lo' : T % 4 ^ k * 4 ^ (i + 1) < 2 ^ 128 := by
    rw [← e64]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hp) (Nat.pow_pos (by decide))
  have d4 : T / 4 ^ k % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize hd : T / 4 ^ k % 4 = d at split d4
  have e1 : 4 ^ k * (d * 4 ^ i) = d * 2 ^ 126 := by rw [Nat.mul_left_comm, e63]
  have e2 : T % 4 ^ k * 4 ^ (i + 1) = T % 4 ^ k * 4 ^ i * 4 := by rw [Nat.pow_succ, Nat.mul_assoc]
  rw [split, Nat.add_mul, Nat.mul_assoc, e1, e2]
  rw [e2] at lo'
  have e3 : T / 4 ^ (k + 1) = T / 4 ^ k / 4 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [e3]
  generalize T % 4 ^ k * 4 ^ i = u at lo lo' ⊢
  generalize T / 4 ^ k = v at hd ⊢
  refine ⟨by omega_using [lo], by omega_using [lo], by omega_using [hd]⟩

/-- The first digit's loop: 64 steps from the remainder and root zero leave `y` (`r18`) and `R`
(`r16`, `r17`) with `y² + R = T` (`T` = the initial `r14`, `r15`) and `R ≤ 2 y`. -/
theorem digit0Loop_ok {s : State} (h8 : s.gpr .r8 = BitVec.ofNat 64 64) (h16 : s.gpr .r16 = BitVec.ofNat 64 0)
    (h17 : s.gpr .r17 = BitVec.ofNat 64 0) (h18 : s.gpr .r18 = BitVec.ofNat 64 0)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.countLoop .r8 VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Step) s fun t =>
      (t.gpr .r18).toNat * (t.gpr .r18).toNat + ((t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat) =
        (s.gpr .r14).toNat * 2 ^ 64 + (s.gpr .r15).toNat ∧
      (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat ≤ 2 * (t.gpr .r18).toNat ∧
      t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      Keep [.r0, .r3, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18] s t := by
  generalize hX : (s.gpr .r14).toNat * 2 ^ 64 + (s.gpr .r15).toNat = X
  have hXl : X < 2 ^ 128 := by have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt; omega_using [hX]
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r15).toNat = X % 4 ^ (64 - i) * 4 ^ i ∧
    (t.gpr .r18).toNat * (t.gpr .r18).toNat + ((t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat) =
      X / 4 ^ (64 - i) ∧
    (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat ≤ 2 * (t.gpr .r18).toNat ∧
    t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
    Keep [.r0, .r3, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18] s t
  have p128 : (4 : Nat) ^ 64 = 2 ^ 128 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  refine WP.mono (wp_countdown (cnt := .r8) (N := 64) (by decide) (by decide) Inv
    (fun i hi t ⟨j14, jr, jle, j20, jm, jk⟩ _ => ?_)
    ⟨by rw [Nat.sub_zero, p128, Nat.mod_eq_of_lt hXl, Nat.pow_zero, Nat.mul_one, hX],
      by rw [h16, h17, h18, Nat.sub_zero, p128, Nat.div_eq_of_lt hXl]; rfl, by rw [h16, h17, h18]; decide,
      h20, rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, tr, tle, t20, tm, tk⟩ => ⟨by rw [tr, Nat.sub_self, Nat.pow_zero, Nat.div_one], tle, t20, tm, tk⟩
  -- The root so far is below `2^i ≤ 2^63`.
  have hY : (t.gpr .r18).toNat < 2 ^ 63 := by
    have h1 : X / 4 ^ (64 - i) < 4 ^ i := by
      refine (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr ?_
      rw [← Nat.pow_add, show i + (64 - i) = 64 by omega_using [hi], p128]; exact hXl
    have h2 : (t.gpr .r18).toNat * (t.gpr .r18).toNat < 2 ^ i * 2 ^ i := by
      rw [← Nat.mul_pow, show 2 * 2 = 4 from rfl]; omega_using [jr, h1]
    have := Nat.mul_self_lt_mul_self_iff.mp h2
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [hi]))
  refine WP.mono (digit0Step_ok j20 hY jle) fun t' ⟨⟨a14, a16, a18, a20, a8, am⟩, ak⟩ => ⟨⟨?_, ?_, ?_, a20,
    by rw [am, jm], jk.trans' ak⟩, a8⟩
  · obtain ⟨b1, -, -⟩ := bits_step (T := X) hi
    rw [a14, j14, b1]
  · obtain ⟨-, b2, b3⟩ := bits_step (T := X) hi
    have hd : (t.gpr .r14).toNat / 2 ^ 62 = X / 4 ^ (64 - (i + 1)) % 4 := by
      rw [← b2, ← j14]; have := (t.gpr .r15).isLt; omega_using []
    rw [a16, a18, hd, b3, ← jr]
    generalize X / 4 ^ (64 - (i + 1)) % 4 = d at hd ⊢
    have d4 : d < 4 := by have := (t.gpr .r14).isLt; omega_using [hd]
    generalize (t.gpr .r18).toNat = y at jle ⊢
    generalize (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat = R at jle ⊢
    have e1 : 2 * y * (2 * y) = 4 * (y * y) := by grind
    have e2 : (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by grind
    split <;> (try rw [e1]) <;> (try rw [e2]) <;> omega_arith
  · rw [a16, a18]
    generalize (t.gpr .r18).toNat = y at jle ⊢
    generalize (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r17).toNat = R at jle ⊢
    have d4 : (t.gpr .r14).toNat / 2 ^ 62 < 4 := by have := (t.gpr .r14).isLt; omega_using []
    split <;> omega_arith

end Digit0

/-! ## `T := R - q̂ D` over the window -/

section MulSub
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs countLoop)

/-- The multiply-and-subtract's loop body. -/
abbrev msBody : List Instr :=
  [.load .d .r7 .r6 0, .mul .r12 .r7 .r18, .mulhu .r0 .r7 .r18, .addc .r12 .r12 .r3, .addze .r3 .r0,
    .load .d .r0 .r5 0, .addc .r10 .r22 .r17, .sube .r0 .r0 .r12, .addze .r22 .r20, .store .d .r0 .r5 0,
    .addi .r5 .r5 8, .addi .r6 .r6 8]

/-- What the loop keeps after `i` words of the window `R` (at `dR`) and of `D` (at `dD`), from `s`:
the pointers, the carry `c` (`r3`) and the borrow as a carry `b` (`r22`, 1 for none), for
`W + q̂ D_{<i} + 2^(64 i) b = R_{<i} + 2^(64 i) (1 + c)`. -/
def MsInv (s : State) (B : Addr) (dR dD : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .r5 = off B (dR + 8 * i) ∧ t.gpr .r6 = off B (dD + 8 * i) ∧ t.gpr .r18 = s.gpr .r18 ∧
    t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.gpr .r17 = BitVec.allOnes 64 ∧ (t.gpr .r22).toNat ≤ 1 ∧
    Outside B dR (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dR i + (s.gpr .r18).toNat * wordsVal s.mem B dD i + 2 ^ (64 * i) * (t.gpr .r22).toNat =
      wordsVal s.mem B dR i + 2 ^ (64 * i) * (1 + (t.gpr .r3).toNat) ∧
    Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r10, .r12, .r22] s t

theorem msWord_ok {s : State} {B : Addr} {Z dR dD n : Nat} (hs : Scr s B Z) (hR : dR + 8 * (n + 1) ≤ Z)
    (hD : dD + 8 * n ≤ Z) (dRD : dD + 8 * n ≤ dR ∨ dR + 8 * (n + 1) ≤ dD) {i : Nat} (hi : i < n) {t : State}
    (hI : MsInv s B dR dD i t) :
    WP isa (.block (msBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      MsInv s B dR dD (i + 1) t' ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j5, j6, j18, j20, j17, jb, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.wr
  have wR : Mont.word t.mem B (dR + 8 * i) = Mont.word s.mem B (dR + 8 * i) := jout.word (by omega_using []) (by omega_using [hR, hi, hnw])
  have wD : Mont.word t.mem B (dD + 8 * i) = Mont.word s.mem B (dD + 8 * i) := jout.word (by omega_using [dRD, hi]) (by omega_using [hD, hi, hnw])
  have rD : t.mem.readW (Mont.off B (dD + 8 * i)) 64 = Mont.word s.mem B (dD + 8 * i) := wD
  have rR : t.mem.readW (Mont.off B (dR + 8 * i)) 64 = Mont.word s.mem B (dR + 8 * i) := wR
  generalize hn : Mont.word s.mem B (dD + 8 * i) = d at rD wD
  generalize hx : Mont.word s.mem B (dR + 8 * i) = x at rR wR
  generalize hl : BitVec.ofNat 64 ((d * t.gpr .r18).toNat + (t.gpr .r3).toNat) = l
  generalize hca : decide (18446744073709551616 ≤ (t.gpr .r22).toNat + (BitVec.allOnes 64).toNat) = ca
  refine WP.mono (WP.keep [.r0, .r3, .r5, .r6, .r7, .r8, .r10, .r12, .r22] (Q := fun t' =>
      t'.gpr .r5 = off B (dR + 8 * i + 8) ∧ t'.gpr .r6 = off B (dD + 8 * i + 8) ∧
      t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
      t'.gpr .r3 = BitVec.ofNat 64 ((BitVec.ofNat 64 (d.toNat * (t.gpr .r18).toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ (d * t.gpr .r18).toNat + (t.gpr .r3).toNat)).toNat) ∧
      t'.gpr .r22 = BitVec.ofNat 64 ((0#64).toNat + (decide (18446744073709551616 ≤ x.toNat +
        (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat) ∧
      t'.mem = t.mem.writeW (off B (dR + 8 * i))
        (BitVec.ofNat 64 (x.toNat + (18446744073709551616 - 1 - l.toNat) + ca.toNat))) (by
    mcrun [exec_adde, BitVec.add_zero, j5, j6, j20, j17, rD, rR, hl, hca,
      hs'.ld (show dR + 8 * i + 8 ≤ Z by omega_using [hR, hi]), hs'.ld (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs'.st (show dR + 8 * i + 8 ≤ Z by omega_using [hR, hi])]) (by decide))
    fun t' ⟨⟨u5, u6, u8, u3, u22, um⟩, uk⟩ => ⟨⟨?_, ?_, by rw [uk.gpr .r18 (by decide), j18],
      by rw [uk.gpr .r20 (by decide), j20], by rw [uk.gpr .r17 (by decide), j17], ?_, ?_, ?_, jk.trans' uk⟩, u8⟩
  · rw [u5, show dR + 8 * i + 8 = dR + 8 * (i + 1) by omega_using []]
  · rw [u6, show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_using []]
  · rw [u22, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl, Nat.zero_add]
    have := Bool.toNat_le (decide (18446744073709551616 ≤ x.toNat + (18446744073709551616 - 1 - l.toNat) + ca.toNat))
    omega_using [this]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside t.mem B (d := dR + 8 * i) _ (by omega_using [hR, hi, hnw])).mono (by omega_using []) (by omega_using []))
  · have km := mul64_arith d (t.gpr .r18) (t.gpr .r3)
    rw [hl, ← u3] at km
    have ks := sube_arith x.toNat l.toNat (t.gpr .r22).toNat x.isLt l.isLt jb
    rw [hca] at ks
    have e22 : (t'.gpr .r22).toNat = (decide (18446744073709551616 ≤ x.toNat +
        (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat := by
      rw [u22, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl, Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide))
    rw [← e22] at ks
    rw [um, fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hR, hi, hnw]), wordsVal_succ_top s.mem B dD i, hn,
      wordsVal_succ_top s.mem B dR i, hx, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
    rw [j18] at km
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize (BitVec.ofNat 64 (x.toNat + (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat = tw at ks ⊢
    generalize (t'.gpr .r22).toNat = b' at ks ⊢
    generalize (t'.gpr .r3).toNat = c' at km ⊢
    generalize l.toNat = ll at km ks
    generalize (s.gpr .r18).toNat = q at km jv ⊢
    generalize d.toNat = dd at km ⊢
    generalize x.toNat = xx at ks ⊢
    generalize (t.gpr .r22).toNat = b at ks jv jb
    generalize (t.gpr .r3).toNat = c at km jv
    generalize wordsVal t.mem B dR i = W at jv ⊢
    generalize wordsVal s.mem B dD i = Dw at jv ⊢
    generalize wordsVal s.mem B dR i = Rw at jv ⊢
    have hin : tw + dd * q + 2 ^ 64 * b' + c + 1 = xx + 2 ^ 64 + b + 2 ^ 64 * c' := by omega_using [ks, km]
    have := congrArg (P * ·) hin
    grind

/-- The multiply-and-subtract after its head: `n` words of `D` (at `dD`, `r6`) times `q̂` (`r18`) from the
`n + 1` words of `R` (at `dR`, `r5`): `W + q̂ D = R + 2^(64 (n + 1)) (1 - b)`, for the borrow `b`. -/
theorem msRest_ok {s : State} {B : Addr} {Z dR dD n : Nat} (hs : Scr s B Z)
    (i5 : s.gpr .r5 = off B dR) (i6 : s.gpr .r6 = off B dD) (i8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (i3 : s.gpr .r3 = BitVec.ofNat 64 0) (i22 : s.gpr .r22 = BitVec.ofNat 64 1)
    (i17 : s.gpr .r17 = BitVec.allOnes 64) (i20 : s.gpr .r20 = BitVec.ofNat 64 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 31) (hR : dR + 8 * (n + 1) ≤ Z)
    (hD : dD + 8 * n ≤ Z) (dRD : dD + 8 * n ≤ dR ∨ dR + 8 * (n + 1) ≤ dD) :
    WP isa (seqs [countLoop .r8 msBody,
        .block [.load .d .r0 .r5 0, .addc .r10 .r22 .r17, .sube .r0 .r0 .r3, .store .d .r0 .r5 0]]) s fun t =>
      (∃ b < 2, wordsVal t.mem B dR (n + 1) + (s.gpr .r18).toNat * wordsVal s.mem B dD n + 2 ^ (64 * (n + 1)) * b =
        wordsVal s.mem B dR (n + 1) + 2 ^ (64 * (n + 1))) ∧
      Outside B dR (8 * (n + 1)) s.mem t.mem ∧ Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r10, .r12, .r22] s t := by
  have hnw := hs.nowrap
  have I0 : MsInv s B dR dD 0 s := ⟨by rw [i5]; rfl, by rw [i6]; rfl, rfl, i20, i17, by rw [i22]; decide,
    Outside.refl _ _ _ _, by simp [wordsVal, i22, i3], Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .r8) (N := n) (by omega_using [hn']) (by omega_using [hn]) (MsInv s B dR dD)
    (fun i hi t hI _ => msWord_ok hs hR hD dRD hi hI) I0 i8)
    fun t ⟨j5, _, j18, j20, j17, jb, jout, jv, jk⟩ => ?_)
  have hs' := hs.congr jk.wr
  have wR : Mont.word t.mem B (dR + 8 * n) = Mont.word s.mem B (dR + 8 * n) := jout.word (by omega_using []) (by omega_using [hR, hnw])
  have rR : t.mem.readW (Mont.off B (dR + 8 * n)) 64 = Mont.word s.mem B (dR + 8 * n) := wR
  generalize hx : Mont.word s.mem B (dR + 8 * n) = x at rR wR
  generalize hca : decide (18446744073709551616 ≤ (t.gpr .r22).toNat + (BitVec.allOnes 64).toNat) = ca
  refine WP.mono (WP.keep [.r0, .r10] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dR + 8 * n)) (BitVec.ofNat 64 (x.toNat +
        (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat))) (by
    mcrun [exec_adde, j5, j17, rR, hca, hs'.ld (show dR + 8 * n + 8 ≤ Z by omega_using [hR]),
      hs'.st (show dR + 8 * n + 8 ≤ Z by omega_using [hR])]) (by decide))
    fun t' ⟨tm, tk⟩ => ⟨?_, ?_, (jk.trans tk).mono (by decide)⟩
  · have ks := sube_arith x.toNat (t.gpr .r3).toNat (t.gpr .r22).toNat x.isLt (t.gpr .r3).isLt jb
    rw [hca] at ks
    rw [tm, fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hR, hnw]), wordsVal_succ_top s.mem B dR n, hx]
    have e1 : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e1]
    have hbl := Bool.toNat_le (decide (18446744073709551616 ≤ x.toNat +
      (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat))
    generalize 2 ^ (64 * n) = P at jv ⊢
    generalize (BitVec.ofNat 64 (x.toNat + (18446744073709551616 - 1 - (t.gpr .r3).toNat) +
      ca.toNat)).toNat = tw at ks ⊢
    generalize (decide (18446744073709551616 ≤ x.toNat +
      (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat)).toNat = b' at ks hbl
    generalize x.toNat = xx at ks ⊢
    generalize (t.gpr .r3).toNat = c at ks jv
    generalize (t.gpr .r22).toNat = b at ks jv jb
    generalize wordsVal t.mem B dR n = W at jv ⊢
    generalize (s.gpr .r18).toNat * wordsVal s.mem B dD n = QD at jv ⊢
    generalize wordsVal s.mem B dR n = Rw at jv ⊢
    rcases (show b' = 0 ∨ b' = 1 by omega_using [hbl]) with rfl | rfl
    · refine ⟨0, by decide, ?_⟩
      have hin : tw + c + 1 = xx + 2 ^ 64 + b := by omega_using [ks]
      have := congrArg (P * ·) hin
      grind
    · refine ⟨1, by decide, ?_⟩
      have hin : tw + c + 2 ^ 64 + 1 = xx + 2 ^ 64 + b := by omega_using [ks]
      have := congrArg (P * ·) hin
      grind
  · rw [tm]
    exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside t.mem B (d := dR + 8 * n) _ (by omega_using [hR, hnw])).mono (by omega_using []) (by omega_using []))

end MulSub

section MaskAdd
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs countLoop)

/-! ## The corrections' masked add -/

theorem mask_and (b : Nat) (hb : b ≤ 1) (d : BitVec 64) :
    (d &&& (0#64 - BitVec.ofNat 64 b)).toNat = b * d.toNat := by
  rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
  · simp
  · rw [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, Nat.one_mul]

theorem ofNat_add_carry (v : Nat) (h : v < 2 ^ 65) :
    (BitVec.ofNat 64 v).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ v)).toNat = v := by
  rw [BitVec.toNat_ofNat]
  by_cases hv : 2 ^ 64 ≤ v
  · simp only [hv, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega_using [h])]
    omega_using [hv]
  · simp only [hv, decide_false, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by omega_using [hv])]
    omega_using []

/-- The masked add's loop body. -/
abbrev maBody : List Instr :=
  [.load .d .r7 .r6 0, .logic .and .r7 .r7 .r9, .load .d .r3 .r5 0, .adde .r3 .r3 .r7,
    .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8]

/-- What the masked add keeps after `i` words: `W + 2^(64 i) CA = T + b D + c₀`. -/
def MaInv (s : State) (B : Addr) (dT dD b : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .r5 = off B (dT + 8 * i) ∧ t.gpr .r6 = off B (dD + 8 * i) ∧ t.gpr .r9 = s.gpr .r9 ∧
    Outside B dT (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dT i + 2 ^ (64 * i) * t.ca.toNat =
      wordsVal s.mem B dT i + b * wordsVal s.mem B dD i + s.ca.toNat ∧
    Keep [.r3, .r5, .r6, .r7, .r8] s t

theorem maWord_ok {s : State} {B : Addr} {Z dT dD n b : Nat} (hs : Scr s B Z) (hT : dT + 8 * n ≤ Z)
    (hD : dD + 8 * n ≤ Z) (dTD : dD + 8 * n ≤ dT ∨ dT + 8 * n ≤ dD) (hb : b ≤ 1)
    (h9 : s.gpr .r9 = 0#64 - BitVec.ofNat 64 b) {i : Nat} (hi : i < n) {t : State}
    (hI : MaInv s B dT dD b i t) :
    WP isa (.block (maBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      MaInv s B dT dD b (i + 1) t' ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j5, j6, j9, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.wr
  have wT : Mont.word t.mem B (dT + 8 * i) = Mont.word s.mem B (dT + 8 * i) := jout.word (by omega_using []) (by omega_using [hT, hi, hnw])
  have wD : Mont.word t.mem B (dD + 8 * i) = Mont.word s.mem B (dD + 8 * i) := jout.word (by omega_using [dTD, hi]) (by omega_using [hD, hi, hnw])
  have rD : t.mem.readW (Mont.off B (dD + 8 * i)) 64 = Mont.word s.mem B (dD + 8 * i) := wD
  have rT : t.mem.readW (Mont.off B (dT + 8 * i)) 64 = Mont.word s.mem B (dT + 8 * i) := wT
  generalize hn : Mont.word s.mem B (dD + 8 * i) = d at rD wD
  generalize hx : Mont.word s.mem B (dT + 8 * i) = x at rT wT
  refine WP.mono (WP.keep [.r3, .r5, .r6, .r7, .r8] (Q := fun t' =>
      t'.gpr .r5 = off B (dT + 8 * i + 8) ∧ t'.gpr .r6 = off B (dD + 8 * i + 8) ∧
      t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
      t'.ca = decide (2 ^ 64 ≤ x.toNat + (d &&& (0#64 - BitVec.ofNat 64 b)).toNat + t.ca.toNat) ∧
      t'.mem = t.mem.writeW (off B (dT + 8 * i))
        (BitVec.ofNat 64 (x.toNat + (d &&& (0#64 - BitVec.ofNat 64 b)).toNat + t.ca.toNat))) (by
    mcrun [exec_adde, BitVec.add_zero, j5, j6, j9, h9, rD, rT,
      hs'.ld (show dT + 8 * i + 8 ≤ Z by omega_using [hT, hi]), hs'.ld (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs'.st (show dT + 8 * i + 8 ≤ Z by omega_using [hT, hi])]) (by decide))
    fun t' ⟨⟨u5, u6, u8, uca, um⟩, uk⟩ => ⟨⟨?_, ?_, by rw [uk.gpr .r9 (by decide), j9], ?_, ?_, jk.trans' uk⟩, u8⟩
  · rw [u5, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_using []]
  · rw [u6, show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_using []]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside t.mem B (d := dT + 8 * i) _ (by omega_using [hT, hi, hnw])).mono (by omega_using []) (by omega_using []))
  · rw [mask_and b hb] at uca um
    have hv : x.toNat + b * d.toNat + t.ca.toNat < 2 ^ 65 := by
      have := x.isLt; have := d.isLt; have := Bool.toNat_le t.ca
      have : b * d.toNat ≤ d.toNat := by rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> omega_using []
      omega_arith
    have ka := ofNat_add_carry _ hv
    rw [← uca] at ka
    rw [um, fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hT, hi, hnw]), wordsVal_succ_top s.mem B dD i, hn,
      wordsVal_succ_top s.mem B dT i, hx, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by
        rw [Nat.mul_succ, Nat.pow_add]]
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize (BitVec.ofNat 64 (x.toNat + b * d.toNat + t.ca.toNat)).toNat = tw at ka ⊢
    generalize t'.ca.toNat = c' at ka ⊢
    generalize t.ca.toNat = c at ka jv
    generalize x.toNat = xx at ka ⊢
    generalize d.toNat = dd at ka ⊢
    generalize wordsVal t.mem B dT i = W at jv ⊢
    generalize wordsVal s.mem B dD i = Dw at jv ⊢
    generalize wordsVal s.mem B dT i = Tw at jv ⊢
    have := congrArg (P * ·) ka
    grind

/-- The masked add's loop: `n` words of `D` (at `dD`, `r6`), masked by `r9 = -b`, added with the
carry `CA` to the `n` words at `dT` (`r5`). -/
theorem maLoop_ok {s : State} {B : Addr} {Z dT dD n b : Nat} (hs : Scr s B Z)
    (i5 : s.gpr .r5 = off B dT) (i6 : s.gpr .r6 = off B dD) (i8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (h9 : s.gpr .r9 = 0#64 - BitVec.ofNat 64 b) (hb : b ≤ 1) (hn : 1 ≤ n) (hn' : n < 2 ^ 31)
    (hT : dT + 8 * n ≤ Z) (hD : dD + 8 * n ≤ Z) (dTD : dD + 8 * n ≤ dT ∨ dT + 8 * n ≤ dD) :
    WP isa (countLoop .r8 maBody) s (MaInv s B dT dD b n) :=
  wp_countdown (cnt := .r8) (N := n) (by omega_using [hn']) (by omega_using [hn]) (MaInv s B dT dD b)
    (fun _ hi _ hI _ => maWord_ok hs hT hD dTD hb h9 hi hI)
    ⟨by rw [i5]; rfl, by rw [i6]; rfl, rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ i8

end MaskAdd

/-! ## The step's pointers -/

section Ptrs
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.RdShift (shl3_val ofNat_sub' off_sub)

/-- `twoH ++ ptrs`, for `w = 4 h + 6` (`r29`) and `j < h` (`r26`): `r11 := 2 h`, `r5 :=` the window's word 0,
`X'`'s word `2 h - 2 j - 2` (`X'` at `dX`, `r19`), `r6 :=` `D`'s word `h - 1 - j` (`D` at `dS`, `r24`). -/
theorem hp_ok {s : State} {B : Addr} {w h j dX dS : Nat} (h29 : s.gpr .r29 = BitVec.ofNat 64 w)
    (hw : w = 4 * h + 6) (hh : h < 2 ^ 20) (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj : j < h)
    (h19 : s.gpr .r19 = off B dX) (h24 : s.gpr .r24 = off B dS) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.twoH ++ VG.Impl.Rsa.PPC64LE.RecoverDet.ptrs)) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 64 (2 * h) ∧ t.gpr .r5 = off B (dX + 8 * (2 * h - 2 * j - 2)) ∧
        t.gpr .r6 = off B (dS + 8 * (h - 1 - j)) ∧ t.mem = s.mem) ∧ Keep [.r5, .r6, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  have e11 : (BitVec.ofNat 64 w - 6#64) >>> 1 = BitVec.ofNat 64 (2 * h) := by
    rw [show (6#64) = BitVec.ofNat 64 6 from rfl, ofNat_sub' (by omega_using [hw]) (by omega_using [hw, hh]),
      show w - 6 = 2 * (2 * h) by omega_using [hw], mont_ofNat_shr1 (by omega_using [hh])]
  have e6 : BitVec.ofNat 64 (2 * h) >>> 1 = BitVec.ofNat 64 h := mont_ofNat_shr1 (by omega_using [hh])
  have a5 : (BitVec.ofNat 64 (2 * h) - BitVec.ofNat 64 j - BitVec.ofNat 64 j) <<< 3 + off B dX - 16#64 =
      off B (dX + 8 * (2 * h - 2 * j - 2)) := by
    rw [ofNat_sub' (by omega_using [hj]) (by omega_using [hh]), ofNat_sub' (by omega_using [hj]) (by omega_using [hh]), shl3_val, BitVec.add_comm,
      off_add, show (16#64) = BitVec.ofNat 64 16 from rfl, off_sub B (by omega_using [hj])]
    congr 1; omega_using [hj]
  have a6 : (BitVec.ofNat 64 h - BitVec.ofNat 64 j) <<< 3 + off B dS - 8#64 = off B (dS + 8 * (h - 1 - j)) := by
    rw [ofNat_sub' (by omega_using [hj]) (by omega_using [hh]), shl3_val, BitVec.add_comm,
      off_add, show (8#64) = BitVec.ofNat 64 8 from rfl, off_sub B (by omega_using [hj])]
    congr 1; omega_using [hj]
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.twoH, VG.Impl.Rsa.PPC64LE.RecoverDet.ptrs, h29, h26, h19, h24, e11, e6,
    a5, a6]

end Ptrs

/-! ## A correction -/

section Correct
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE

/-- The correction's head after the pointers. -/
abbrev corrHead : List Instr :=
  [.li .r20 0, .lsl .r3 .r26 3, .add .r3 .r3 .r5, .load .d .r0 .r3 16,
    .lsr .d .r0 .r0 63, .sub .r9 .r20 .r0, .add .r10 .r18 .r18, .subi .r10 .r10 1, .subi .r14 .r18 1,
    .lsr .d .r14 .r14 63, .load .d .r3 .r5 0, .logic .and .r10 .r10 .r9, .addc .r3 .r3 .r10,
    .store .d .r3 .r5 0, .load .d .r7 .r6 8, .logic .or .r7 .r7 .r14, .logic .and .r7 .r7 .r9,
    .load .d .r3 .r5 8, .adde .r3 .r3 .r7, .store .d .r3 .r5 8, .addi .r5 .r5 16, .addi .r6 .r6 16,
    .add .r18 .r18 .r9, .addi .r8 .r26 0]

theorem corrHead_raw {s : State} {B : Addr} {Z dT dD j : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dT) (h6 : s.gpr .r6 = off B dD) (h26 : s.gpr .r26 = BitVec.ofNat 64 j)
    (hj : j < 2 ^ 20) (hT : dT + 8 * (j + 3) ≤ Z) (hD : dD + 16 ≤ Z) (dTD : dD + 16 ≤ dT ∨ dT + 8 * (j + 3) ≤ dD) :
    WP isa (.block corrHead) s fun t =>
      let x0 := Mont.word s.mem B dT
      let x1 := Mont.word s.mem B (dT + 8)
      let mk := 0#64 - Mont.word s.mem B (dT + 8 * j + 16) >>> 63
      let q := s.gpr .r18
      let v0 := x0.toNat + ((q + q - 1#64) &&& mk).toNat
      let v1 := x1.toNat + ((Mont.word s.mem B (dD + 8) ||| (q - 1#64) >>> 63) &&& mk).toNat +
        (decide (2 ^ 64 ≤ v0)).toNat
      (t.gpr .r5 = off B (dT + 16) ∧ t.gpr .r6 = off B (dD + 16) ∧ t.gpr .r8 = BitVec.ofNat 64 j ∧
        t.gpr .r9 = mk ∧ t.gpr .r18 = q + mk ∧ t.gpr .r20 = 0#64 ∧ t.ca = decide (2 ^ 64 ≤ v1) ∧
        t.mem = (s.mem.writeW (off B dT) (BitVec.ofNat 64 v0)).writeW (off B (dT + 8)) (BitVec.ofNat 64 v1)) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r14, .r18, .r20] s t := by
  have hnw := hs.nowrap
  have e3 : BitVec.ofNat 64 j <<< 3 + off B dT = off B (dT + 8 * j) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.shl3_val, BitVec.add_comm, off_add]
  have w1 : ∀ v : BitVec 64, (s.mem.writeW (off B dT) v).readW (off B (dT + 8)) 64 = Mont.word s.mem B (dT + 8) :=
    fun v => (writeW_outside s.mem B (d := dT) v (by omega)).word (by omega_using []) (by omega_using [hT, hnw])
  have w2 : ∀ v : BitVec 64, (s.mem.writeW (off B dT) v).readW (off B (dD + 8)) 64 = Mont.word s.mem B (dD + 8) :=
    fun v => (writeW_outside s.mem B (d := dT) v (by omega_using [hT, hnw])).word (by omega_using [dTD]) (by omega_using [hD, hnw])
  refine WP.keep _ ?_ (by decide)
  mcrun [exec_adde, BitVec.add_zero, h5, h6, h26, e3, w1, w2,
    hs.ld (show dT + 8 * j + 16 + 8 ≤ Z by omega_using [hT]), hs.ld (show dT + 8 ≤ Z by omega_using [hT]),
    hs.ld (show dT + 8 + 8 ≤ Z by omega_using [hT]), hs.ld (show dD + 8 + 8 ≤ Z by omega_using [hD]),
    hs.st (show dT + 8 ≤ Z by omega_using [hT]), hs.st (show dT + 8 + 8 ≤ Z by omega_using [hT])]

theorem two_q_sub (q : BitVec 64) (hq : 1 ≤ q.toNat) :
    (q + q - 1#64).toNat + 2 ^ 64 * ((q - 1#64).toNat / 2 ^ 63) = 2 * q.toNat - 1 := by
  have := q.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega_using [hq]

theorem or_bit (d b : BitVec 64) (hd : d.toNat % 2 = 0) (hb : b.toNat ≤ 1) : (d ||| b).toNat = d.toNat + b.toNat := by
  have hand : d &&& b = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega_using [hb]) with h | h <;> rw [h]
    · simp
    · rw [Nat.and_one_is_mod, hd]; rfl
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add]
  have := d.isLt
  rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega_using [hb]) with h | h <;> rw [h] <;> omega_arith

/-- The correction's head after the pointers: the sign `neg` of the window's top word (`dT`'s word `j + 2`)
as the mask `r9`, `q̂ := q̂ - neg`, and the window's words 0 and 1 plus `neg (2 q̂ - 1 + β D₁)` with a carry,
for an even `D₁` (`D`'s word 1). -/
theorem corrHead_ok {s : State} {B : Addr} {Z dT dD j : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dT) (h6 : s.gpr .r6 = off B dD) (h26 : s.gpr .r26 = BitVec.ofNat 64 j)
    (hj : j < 2 ^ 20) (hT : dT + 8 * (j + 3) ≤ Z) (hD : dD + 16 ≤ Z) (dTD : dD + 16 ≤ dT ∨ dT + 8 * (j + 3) ≤ dD)
    (hq : (Mont.word s.mem B (dT + 8 * j + 16)).toNat / 2 ^ 63 = 1 → 1 ≤ (s.gpr .r18).toNat)
    (hd1 : (Mont.word s.mem B (dD + 8)).toNat % 2 = 0) :
    WP isa (.block corrHead) s fun t =>
      let neg := (Mont.word s.mem B (dT + 8 * j + 16)).toNat / 2 ^ 63
      (t.gpr .r5 = off B (dT + 16) ∧ t.gpr .r6 = off B (dD + 16) ∧ t.gpr .r8 = BitVec.ofNat 64 j ∧
        t.gpr .r9 = 0#64 - BitVec.ofNat 64 neg ∧ (t.gpr .r18).toNat = (s.gpr .r18).toNat - neg ∧
        t.gpr .r20 = 0#64 ∧ Outside B dT 16 s.mem t.mem ∧
        wordsVal t.mem B dT 2 + 2 ^ 128 * t.ca.toNat = wordsVal s.mem B dT 2 +
          neg * (2 * (s.gpr .r18).toNat - 1 + 2 ^ 64 * (Mont.word s.mem B (dD + 8)).toNat)) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r14, .r18, .r20] s t := by
  have hnw := hs.nowrap
  refine WP.mono (corrHead_raw hs h5 h6 h26 hj hT hD dTD) fun t ⟨⟨t5, t6, t8, t9, t18, t20, tca, tm⟩, tk⟩ => ?_
  simp only [VG.Proof.Rsa.PPC64LE.RdShift.shr63_ofNat] at t9 t18 tca tm
  have hneg : (Mont.word s.mem B (dT + 8 * j + 16)).toNat / 2 ^ 63 ≤ 1 := by
    have := (Mont.word s.mem B (dT + 8 * j + 16)).isLt; omega_using []
  generalize (Mont.word s.mem B (dT + 8 * j + 16)).toNat / 2 ^ 63 = neg at hneg hq t9 t18 tca tm ⊢
  have ev : ∀ v0 v1 : Nat, v0 < 2 ^ 65 → v1 < 2 ^ 65 →
      wordsVal ((s.mem.writeW (off B dT) (BitVec.ofNat 64 v0)).writeW (off B (dT + 8)) (BitVec.ofNat 64 v1)) B dT 2 +
        2 ^ 128 * (decide (2 ^ 64 ≤ v1)).toNat = v0 - 2 ^ 64 * (decide (2 ^ 64 ≤ v0)).toNat + 2 ^ 64 * v1 := by
    intro v0 v1 h0 h1
    have k0 := ofNat_add_carry v0 h0
    have k1 := ofNat_add_carry v1 h1
    rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low,
      word_writeW_self, (writeW_outside _ B (d := dT + 8) _ (by omega_using [hT, hnw])).word (by omega_using []) (by omega_using [hT, hnw]), word_writeW_self]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    omega_using [k0, k1]
  refine ⟨⟨t5, t6, t8, t9, ?_, t20, ?_, ?_⟩, tk⟩
  · rw [t18]
    rcases (show neg = 0 ∨ neg = 1 by omega_using [hneg]) with rfl | rfl
    · simp
    · rw [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.toNat_add, BitVec.toNat_allOnes]
      have := hq rfl; have := (s.gpr .r18).isLt; omega_using [hq]
  · rw [tm]
    exact ((writeW_outside s.mem B (d := dT) _ (by omega_using [hT, hnw])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ B (d := dT + 8) _ (by omega_using [hT, hnw])).mono (by omega_using []) (by omega_using []))
  · rw [tca, tm]
    have es : wordsVal s.mem B dT 2 = (Mont.word s.mem B dT).toNat + 2 ^ 64 * (Mont.word s.mem B (dT + 8)).toNat := by
      rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low]
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    have hx0 := (Mont.word s.mem B dT).isLt
    have hx1 := (Mont.word s.mem B (dT + 8)).isLt
    have hd := (Mont.word s.mem B (dD + 8)).isLt
    rcases (show neg = 0 ∨ neg = 1 by omega_using [hneg]) with rfl | rfl
    · simp only [show 0#64 - BitVec.ofNat 64 0 = 0#64 by decide, BitVec.and_zero, BitVec.toNat_zero, Nat.add_zero,
        show ¬ 2 ^ 64 ≤ (Mont.word s.mem B dT).toNat by omega_using [], decide_false, Bool.toNat_false]
      rw [ev _ _ (by omega_using []) (by omega_using []), es]
      simp only [show ¬ 2 ^ 64 ≤ (Mont.word s.mem B dT).toNat by omega_using [], decide_false, Bool.toNat_false]
      omega_using []
    · have hq1 := hq rfl
      have h2 := two_q_sub (s.gpr .r18) hq1
      have hbit : (BitVec.ofNat 64 ((s.gpr .r18 - 1#64).toNat / 2 ^ 63)).toNat ≤ 1 := by
        rw [BitVec.toNat_ofNat]
        have := (s.gpr .r18 - 1#64).isLt; omega_using []
      simp only [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
      rw [or_bit _ _ hd1 hbit]
      have hl := (s.gpr .r18 + s.gpr .r18 - 1#64).isLt
      have e8 : (BitVec.ofNat 64 ((s.gpr .r18 - 1#64).toNat / 2 ^ 63)).toNat = (s.gpr .r18 - 1#64).toNat / 2 ^ 63 := by
        rw [BitVec.toNat_ofNat]; have := (s.gpr .r18 - 1#64).isLt; omega_using []
      rw [e8] at hbit ⊢
      have hc0 := Bool.toNat_le (decide (2 ^ 64 ≤ (Mont.word s.mem B dT).toNat + (s.gpr .r18 + s.gpr .r18 - 1#64).toNat))
      rw [ev _ _ (by omega_using []) (by omega), es]
      generalize (s.gpr .r18 + s.gpr .r18 - 1#64).toNat = L at h2 hl ⊢
      generalize (s.gpr .r18 - 1#64).toNat / 2 ^ 63 = hb at h2 hbit ⊢
      generalize (Mont.word s.mem B dT).toNat = x0 at hx0 ⊢
      have := Bool.toNat_le (decide (2 ^ 64 ≤ x0 + L))
      have hc : 2 ^ 64 * (decide (2 ^ 64 ≤ x0 + L)).toNat ≤ x0 + L := by
        by_cases h : 2 ^ 64 ≤ x0 + L
        · simp only [h, decide_true, Bool.toNat_true]; omega_using [h]
        · simp only [h, decide_false, Bool.toNat_false]; omega_using []
      omega_using [h2, hc]

/-- The registers a correction changes. -/
abbrev corrRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r14, .r18, .r20]

theorem corr_arith {W2 W2' ca2 ng q2 d1 M M3 ca3 Dm P x tw c3 : Nat}
    (qv : W2' + 2 ^ 128 * ca2 = W2 + ng * (q2 + 2 ^ 64 * d1))
    (jv : M3 + P * ca3 = M + ng * Dm + ca2) (kt : tw + 2 ^ 64 * c3 = x + ca3) :
    W2' + 2 ^ 128 * (M3 + P * tw) + 2 ^ 128 * (P * 2 ^ 64) * c3 =
      W2 + 2 ^ 128 * (M + P * x) + ng * (q2 + 2 ^ 64 * (d1 + 2 ^ 64 * Dm)) := by
  have k2 := congrArg ((2 ^ 128 * P) * ·) kt
  have j2 := congrArg (2 ^ 128 * ·) jv
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num] at *
  generalize (2 : Nat) ^ 64 = b at *
  linear_combination qv + j2 + k2

/-- A correction at step `j` (`1 ≤ j < h`): the window `T` (`X'`'s words `2 h - 2 j - 2 …`, `j + 3` of them)
plus `neg (2 q̂ - 1 + β D)`, `D` the `j + 1` words above `D`'s word `h - 1 - j`, and `q̂ := q̂ - neg`, for
the sign `neg` of `T`'s top word, modulo `2^(64 (j + 3))`. -/
theorem correct_ok {s : State} {B : Addr} {Z w h j dX dS dT dD : Nat} (hs : Scr s B Z)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 w) (hw : w = 4 * h + 6) (hh : h < 2 ^ 20)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj1 : 1 ≤ j) (hj : j < h)
    (h19 : s.gpr .r19 = off B dX) (h24 : s.gpr .r24 = off B dS)
    (hX : dX + 8 * (2 * h) ≤ Z) (hS : dS + 8 * (h + 1) ≤ Z) (dXS : dS + 8 * (h + 1) ≤ dX ∨ dX + 8 * (2 * h) ≤ dS)
    (hdT : dT = dX + 8 * (2 * h - 2 * j - 2)) (hdD : dD = dS + 8 * (h - 1 - j))
    (hq : (Mont.word s.mem B (dT + 8 * (j + 2))).toNat / 2 ^ 63 = 1 → 1 ≤ (s.gpr .r18).toNat)
    (hd1 : (Mont.word s.mem B (dD + 8)).toNat % 2 = 0) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.correct s fun t =>
      let neg := (Mont.word s.mem B (dT + 8 * (j + 2))).toNat / 2 ^ 63
      (∃ c < 2, wordsVal t.mem B dT (j + 3) + 2 ^ (64 * (j + 3)) * c = wordsVal s.mem B dT (j + 3) +
          neg * (2 * (s.gpr .r18).toNat - 1 + 2 ^ 64 * wordsVal s.mem B (dD + 8) (j + 1))) ∧
        (t.gpr .r18).toNat = (s.gpr .r18).toNat - neg ∧ t.gpr .r20 = 0#64 ∧
        Outside B dT (8 * (j + 3)) s.mem t.mem ∧ Keep corrRegs s t := by
  have hnw := hs.nowrap
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.correct
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (hp_ok h29 hw hh h26 hj h19 h24)
    fun s1 ⟨⟨_, p5, p6, pm⟩, pk⟩ => ?_))
  rw [← hdT] at p5
  rw [← hdD] at p6
  have hs1 := hs.congr pk.wr
  have e26 : s1.gpr .r26 = BitVec.ofNat 64 j := (pk.gpr _ (by decide)).trans h26
  have hq1 : (Mont.word s1.mem B (dT + 8 * j + 16)).toNat / 2 ^ 63 = 1 → 1 ≤ (s1.gpr .r18).toNat := by
    rw [pm, pk.gpr .r18 (by decide), show dT + 8 * j + 16 = dT + 8 * (j + 2) by omega_using []]
    exact hq
  have hd1' : (Mont.word s1.mem B (dD + 8)).toNat % 2 = 0 := by rw [pm]; exact hd1
  refine WP.mono (corrHead_ok hs1 p5 p6 e26 (by omega_using [hh, hj]) (by omega_using [hj1, hj, hX, hdT]) (by omega_using [hj, hS, hdD]) (by omega_using [hj1, hj, dXS, hdT, hdD]) hq1 hd1')
    fun s2 ⟨⟨q5, q6, q8, q9, q18, q20, qout, qv⟩, qk⟩ => ?_
  rw [pm, show dT + 8 * j + 16 = dT + 8 * (j + 2) by omega_using []] at q9 q18 qv
  rw [pm] at qout
  rw [pk.gpr .r18 (by decide)] at q18 qv
  have hneg : (Mont.word s.mem B (dT + 8 * (j + 2))).toNat / 2 ^ 63 ≤ 1 := by
    have := (Mont.word s.mem B (dT + 8 * (j + 2))).isLt; omega_using []
  have hs2 := hs1.congr qk.wr
  refine WP.seq (WP.mono (maLoop_ok hs2 q5 q6 q8 q9 hneg hj1 (by omega_using [hh, hj]) (by omega_using [hj, hX, hdT]) (by omega_using [hj, hS, hdD]) (by omega_using [hj, dXS, hdT, hdD]))
    fun s3 ⟨j5, _, _, jout, jv, jk⟩ => ?_)
  have hs3 := hs2.congr jk.wr
  -- What the head and the loop left.
  have eT : ∀ k, k ≤ j → wordsVal s2.mem B (dT + 16) k = wordsVal s.mem B (dT + 16) k := fun k hk =>
    qout.wordsVal (by omega_using []) (by omega_using [hj, hX, hdT, hnw, hk])
  have eD : wordsVal s2.mem B (dD + 16) j = wordsVal s.mem B (dD + 16) j := qout.wordsVal (by omega_using [hj, dXS, hdT, hdD]) (by omega_using [hj, hS, hdD, hnw])
  have xt3 : Mont.word s3.mem B (dT + 16 + 8 * j) = Mont.word s.mem B (dT + 8 * (j + 2)) := by
    rw [jout.word (by omega_using []) (by omega_using [hj1, hj, hX, hdT, hnw]), show dT + 16 + 8 * j = dT + 8 * (j + 2) by omega_using []]
    exact qout.word (by omega_using []) (by omega_using [hj1, hj, hX, hdT, hnw])
  have rt : s3.mem.readW (Mont.off B (dT + 16 + 8 * j)) 64 = Mont.word s.mem B (dT + 8 * (j + 2)) := xt3
  generalize hxt : Mont.word s.mem B (dT + 8 * (j + 2)) = xt at rt hneg q9 q18 qv hq jv ⊢
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s3.mem.writeW (off B (dT + 16 + 8 * j))
      (BitVec.ofNat 64 (xt.toNat + s3.ca.toNat))) (by
    mcrun [j5, rt, hs3.ld (show dT + 16 + 8 * j + 8 ≤ Z by omega_using [hj1, hj, hX, hdT]),
      hs3.st (show dT + 16 + 8 * j + 8 ≤ Z by omega_using [hj1, hj, hX, hdT])]) (by decide))
    fun t ⟨tm, tk⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hca3 := Bool.toNat_le s3.ca
    have kt := ofNat_add_carry (xt.toNat + s3.ca.toNat) (by have := xt.isLt; omega_using [hca3])
    refine ⟨(decide (2 ^ 64 ≤ xt.toNat + s3.ca.toNat)).toNat, Nat.lt_succ_of_le (Bool.toNat_le _), ?_⟩
    have eL : wordsVal t.mem B dT (j + 3) = wordsVal s2.mem B dT 2 + 2 ^ 128 * (wordsVal s3.mem B (dT + 16) j +
        2 ^ (64 * j) * (BitVec.ofNat 64 (xt.toNat + s3.ca.toNat)).toNat) := by
      rw [show j + 3 = 2 + (j + 1) by omega_using [], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, tm,
        show dT + 8 * 2 = dT + 16 by omega_using [], fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hj1, hj, hX, hdT, hnw]),
        (writeW_outside s3.mem B (d := dT + 16 + 8 * j) _ (by omega_using [hj1, hj, hX, hdT, hnw])).wordsVal (by omega_using []) (by omega_using [hj, hX, hdT, hnw]),
        jout.wordsVal (by omega_using []) (by omega_using [hj, hX, hdT, hnw])]
    have eR : wordsVal s.mem B dT (j + 3) = wordsVal s.mem B dT 2 + 2 ^ 128 * (wordsVal s.mem B (dT + 16) j +
        2 ^ (64 * j) * xt.toNat) := by
      rw [show j + 3 = 2 + (j + 1) by omega_using [], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append,
        show dT + 8 * 2 = dT + 16 by omega_using [], wordsVal_succ_top s.mem B (dT + 16) j,
        show dT + 16 + 8 * j = dT + 8 * (j + 2) by omega_using [], hxt]
    have eDv : wordsVal s.mem B (dD + 8) (j + 1) =
        (Mont.word s.mem B (dD + 8)).toNat + 2 ^ 64 * wordsVal s.mem B (dD + 16) j := by
      rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low]
    rw [eT j (Nat.le_refl _), eD] at jv
    rw [eL, eR, eDv, show 2 ^ (64 * (j + 3)) = 2 ^ 128 * (2 ^ (64 * j) * 2 ^ 64) by
      rw [show 64 * (j + 3) = 128 + (64 * j + 64) by omega_using [], Nat.pow_add, Nat.pow_add]]
    exact corr_arith qv jv kt
  · rw [tk.gpr .r18 (by decide), jk.gpr .r18 (by decide), q18]
  · rw [tk.gpr .r20 (by decide), jk.gpr .r20 (by decide), q20]
  · rw [tm]
    exact ((qout.mono (by omega_using []) (by omega_using [])).trans (jout.mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B (d := dT + 16 + 8 * j) _ (by omega_using [hj1, hj, hX, hdT, hnw])).mono (by omega_using []) (by omega_using []))
  · exact ((((pk.trans qk).trans jk).trans tk)).mono (by decide)


end Correct

/-! ## The step's multiply-and-subtract -/

section MulSubD
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE

/-- `mulSubD` at step `j` (`1 ≤ j < h`): `D`'s word `h - 1 - j` (at `dD`) `:= q̂`, then the window `T` (`j + 3`
words at `dT`) `:= T - q̂ D` for `D`'s `j + 2` words at `dD`, modulo `2^(64 (j + 3))`. -/
theorem mulSubD_ok {s : State} {B : Addr} {Z w h j dX dS dT dD : Nat} (hs : Scr s B Z)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 w) (hw : w = 4 * h + 6) (hh : h < 2 ^ 20)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj1 : 1 ≤ j) (hj : j < h)
    (h19 : s.gpr .r19 = off B dX) (h24 : s.gpr .r24 = off B dS)
    (hX : dX + 8 * (2 * h) ≤ Z) (hS : dS + 8 * (h + 1) ≤ Z) (dXS : dS + 8 * (h + 1) ≤ dX ∨ dX + 8 * (2 * h) ≤ dS)
    (hdT : dT = dX + 8 * (2 * h - 2 * j - 2)) (hdD : dD = dS + 8 * (h - 1 - j)) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.mulSubD s fun t =>
      (∃ b < 2, wordsVal t.mem B dT (j + 3) + (s.gpr .r18).toNat * wordsVal (s.mem.writeW (off B dD) (s.gpr .r18)) B dD (j + 2) +
          2 ^ (64 * (j + 3)) * b = wordsVal s.mem B dT (j + 3) + 2 ^ (64 * (j + 3))) ∧
        Outside B dT (8 * (j + 3)) (s.mem.writeW (off B dD) (s.gpr .r18)) t.mem ∧ t.gpr .r20 = 0#64 ∧
        Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r10, .r11, .r12, .r17, .r20, .r22] s t := by
  have hnw := hs.nowrap
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.mulSubD
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (hp_ok h29 hw hh h26 hj h19 h24)
    fun s1 ⟨⟨_, p5, p6, pm⟩, pk⟩ => ?_))
  rw [← hdT] at p5
  rw [← hdD] at p6
  have hs1 := hs.congr pk.wr
  have e26 : s1.gpr .r26 = BitVec.ofNat 64 j := (pk.gpr _ (by decide)).trans h26
  have e18 : s1.gpr .r18 = s.gpr .r18 := pk.gpr _ (by decide)
  refine WP.mono (WP.keep [.r3, .r8, .r17, .r20, .r22] (Q := fun u =>
      u.gpr .r3 = BitVec.ofNat 64 0 ∧ u.gpr .r8 = BitVec.ofNat 64 (j + 2) ∧ u.gpr .r17 = BitVec.allOnes 64 ∧
        u.gpr .r20 = BitVec.ofNat 64 0 ∧ u.gpr .r22 = BitVec.ofNat 64 1 ∧ u.mem = s.mem.writeW (off B dD) (s.gpr .r18)) (by
    mcrun [p6, e26, e18, pm, hs1.st (show dD + 8 ≤ Z by omega_using [hS, hdD])]
    exact ⟨BitVec.eq_of_toNat_eq (by simp), by decide⟩) (by decide))
    fun s2 ⟨⟨u3, u8, u17, u20, u22, um⟩, uk⟩ => ?_
  have hs2 := hs1.congr uk.wr
  have q5 : s2.gpr .r5 = off B dT := (uk.gpr _ (by decide)).trans p5
  have q6 : s2.gpr .r6 = off B dD := (uk.gpr _ (by decide)).trans p6
  have q18 : s2.gpr .r18 = s.gpr .r18 := (uk.gpr _ (by decide)).trans e18
  refine WP.mono (msRest_ok hs2 q5 q6 u8 u3 u22 u17 u20 (by omega_using []) (by omega_using [hh, hj]) (by omega_using [hj1, hj, hX, hdT]) (by omega_using [hj, hS, hdD]) (by omega_using [hj1, hj, dXS, hdT, hdD]))
    fun t ⟨⟨b, hb, hv⟩, tout, tk⟩ => ⟨⟨b, hb, ?_⟩, by rw [← um]; exact tout,
      by rw [tk.gpr .r20 (by decide), u20], ((pk.trans uk).trans tk).mono (by decide)⟩
  rw [q18, um, (writeW_outside s.mem B (d := dD) _ (by omega_using [hS, hdD, hnw])).wordsVal (d := dT) (k := j + 3) (by omega_using [hj1, hj, dXS, hdT, hdD])
    (by omega_using [hj1, hj, hX, hdT, hnw])] at hv
  exact hv

/-- `finishQ` at step `j` (`j < h`): `D`'s words `h - 1 - j` and `h - j` (at `dD`) `:= 2 q̂` and plus its
carry, for an even word `h - j`: `D := 2 s'`; `j + 1`, and one step fewer. -/
theorem finishQ_ok {s : State} {B : Addr} {Z w h j dX dS dD : Nat} (hs : Scr s B Z)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 w) (hw : w = 4 * h + 6) (hh : h < 2 ^ 20)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj : j < h)
    (h19 : s.gpr .r19 = off B dX) (h24 : s.gpr .r24 = off B dS)
    (hS : dS + 8 * (h + 1) ≤ Z) (hdD : dD = dS + 8 * (h - 1 - j))
    (hd1 : (Mont.word s.mem B (dD + 8)).toNat % 2 = 0) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.finishQ) s fun t =>
      wordsVal t.mem B dD 2 = 2 * (s.gpr .r18).toNat + 2 ^ 64 * (Mont.word s.mem B (dD + 8)).toNat ∧
        (Mont.word t.mem B dD).toNat % 2 = 0 ∧ Outside B dD 16 s.mem t.mem ∧
        t.gpr .r26 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r28 = s.gpr .r28 - BitVec.ofNat 64 1 ∧
        Keep [.r0, .r3, .r5, .r6, .r11, .r26, .r28] s t := by
  have hnw := hs.nowrap
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.finishQ
  rw [WP.block_append_iff]
  refine WP.mono (hp_ok h29 hw hh h26 hj h19 h24) fun s1 ⟨⟨_, _, p6, pm⟩, pk⟩ => ?_
  rw [← hdD] at p6
  have hs1 := hs.congr pk.wr
  have e18 : s1.gpr .r18 = s.gpr .r18 := pk.gpr _ (by decide)
  have e26 : s1.gpr .r26 = BitVec.ofNat 64 j := (pk.gpr _ (by decide)).trans h26
  have e28 : s1.gpr .r28 = s.gpr .r28 := pk.gpr _ (by decide)
  have w2 : ∀ v : BitVec 64, (s.mem.writeW (off B dD) v).readW (off B (dD + 8)) 64 = Mont.word s.mem B (dD + 8) :=
    fun v => (writeW_outside s.mem B (d := dD) v (by omega_using [hS, hdD, hnw])).word (by omega_using []) (by omega_using [hj, hS, hdD, hnw])
  refine WP.mono (WP.keep [.r0, .r3, .r26, .r28] (Q := fun t =>
      t.gpr .r26 = BitVec.ofNat 64 j + 1#64 ∧ t.gpr .r28 = s.gpr .r28 - 1#64 ∧
      t.mem = (s.mem.writeW (off B dD) (s.gpr .r18 + s.gpr .r18)).writeW (off B (dD + 8))
        (Mont.word s.mem B (dD + 8) + s.gpr .r18 >>> 63)) (by
    mcrun [p6, e18, e26, e28, pm, w2, hs1.ld (show dD + 8 + 8 ≤ Z by omega_using [hj, hS, hdD]), hs1.st (show dD + 8 ≤ Z by omega_using [hS, hdD]),
      hs1.st (show dD + 8 + 8 ≤ Z by omega_using [hj, hS, hdD])]) (by decide))
    fun t ⟨⟨t26, t28, tm⟩, tk⟩ => ⟨?_, ?_, ?_, ?_, t28, (pk.trans tk).mono (by decide)⟩
  · have hq := (s.gpr .r18).isLt
    have hd := (Mont.word s.mem B (dD + 8)).isLt
    rw [tm, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low,
      word_writeW_self, (writeW_outside _ B (d := dD + 8) _ (by omega_using [hj, hS, hdD, hnw])).word (by omega_using []) (by omega_using [hS, hdD, hnw]), word_writeW_self]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    omega_using [hd1]
  · rw [tm, (writeW_outside _ B (d := dD + 8) _ (by omega_using [hj, hS, hdD, hnw])).word (by omega_using []) (by omega_using [hS, hdD, hnw]), word_writeW_self,
      BitVec.toNat_add]
    omega_using []
  · rw [tm]
    exact ((writeW_outside s.mem B (d := dD) _ (by omega_using [hS, hdD, hnw])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ B (d := dD + 8) _ (by omega_using [hj, hS, hdD, hnw])).mono (by omega_using []) (by omega_using []))
  · rw [t26]; apply BitVec.eq_of_toNat_eq; simp

end MulSubD

/-! ## The estimate -/

section Estimate
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.Precompute (quotMG quotFix quot3)
open VG.Proof.Rsa.PPC64LE.Keys (Ws ptr_ok)
open VG.Proof.Rsa.KeyWorkspace (arr S)

/-- `quotMG ++ quotFix` in registers: `q̂ := min(⌊(u₂ β + u₁) / d'⌋, β - 1)` (`r18`) for `u₂ ≤ d'` (`r15`, `r16`,
`r7`), `d' ≥ 2^63`, its reciprocal `v` in `r18`, `r22 = d' - u₂` and zero in `r20`. -/
theorem mgFix_ok {s : State} (hd63 : 2 ^ 63 ≤ (s.gpr .r7).toNat)
    (hv : (s.gpr .r18).toNat = (2 ^ 128 - 1) / (s.gpr .r7).toNat - 2 ^ 64) (h20 : s.gpr .r20 = BitVec.ofNat 64 0)
    (h22 : s.gpr .r22 = s.gpr .r7 - s.gpr .r15) (hu : (s.gpr .r15).toNat ≤ (s.gpr .r7).toNat) :
    WP isa (.block (quotMG ++ quotFix)) s fun t =>
      ((t.gpr .r18).toNat = min (((s.gpr .r15).toNat * 2 ^ 64 + (s.gpr .r16).toNat) / (s.gpr .r7).toNat)
        (2 ^ 64 - 1) ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r12, .r17, .r18] s t := by
  generalize hD : s.gpr .r7 = D at hd63 hv h22 hu ⊢
  generalize hV : s.gpr .r18 = V at hv
  have hDlt := D.isLt
  have hd0 : 0 < D.toNat := by omega_using [hd63]
  refine WP.block_append (WP.mono (WP.keep [.r0, .r3, .r12, .r17, .r18] (Q := fun t =>
      t.gpr .r18 = mgqP V (s.gpr .r15) (s.gpr .r16) D ∧ t.mem = s.mem) (by
      unfold quotMG
      mcrun [exec_adde, hD, hV, h20]
      rfl) (by decide)) fun s₂ ⟨⟨b18, m2⟩, k2⟩ => ?_)
  have hst : WP isa (.block quotFix) s₂ fun t' =>
      (t'.gpr .r18 = (if s.gpr .r22 = 0#64 then BitVec.allOnes 64 else s₂.gpr .r18) ∧ t'.mem = s₂.mem) ∧
        Keep [.r12, .r18] s₂ t' := by
    refine WP.keep _ ?_ (by decide)
    unfold quotFix
    mcrun [(k2.gpr .r20 (by decide)).trans h20, (k2.gpr .r22 (by decide)), quotFix_val]
  refine WP.mono hst fun t ⟨⟨u18, um⟩, uk⟩ => ⟨⟨?_, by rw [um, m2]⟩, (k2.trans uk).mono (by decide)⟩
  have hfix := VG.Proof.Bignum.WordStep.qhat_fix hd0 hu (s.gpr .r16).isLt
  rw [← hfix, u18]
  by_cases hc : (s.gpr .r15).toNat = D.toNat
  · have : s.gpr .r22 = 0#64 := by
      rw [h22, bv_sub_eq_zero]; exact BitVec.eq_of_toNat_eq hc.symm
    rw [ite_eq_left_iff.mpr fun h => absurd this h, ite_eq_left_iff.mpr fun h => absurd hc h, BitVec.toNat_allOnes]
  · have : ¬ s.gpr .r22 = 0#64 := by
      rw [h22, bv_sub_eq_zero]; intro h; exact hc (by rw [h])
    rw [ite_eq_right_iff.mpr fun h => absurd h this, ite_eq_right_iff.mpr fun h => absurd h hc, b18]
    have hlt : (s.gpr .r15).toNat < D.toNat := Nat.lt_of_le_of_ne hu hc
    have hq := mgqP_val (v := V.toNat) (u := (s.gpr .r15).toNat) (a := (s.gpr .r16).toNat) hDlt hd63 hlt
      (s.gpr .r16).isLt hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
    exact hq

/-- The estimate's middle, after the pointers. -/
abbrev estMid : List Instr :=
  [.lsl .r0 .r11 2, .add .r3 .r0 .r24, .subi .r3 .r3 16, .load .d .r10 .r3 0, .load .d .r12 .r3 8,
    .lsr .d .r10 .r10 1, .lsl .r12 .r12 63, .add .r10 .r10 .r12, .store .d .r10 .r9 24,
    .lsl .r3 .r26 3, .add .r3 .r3 .r5, .subi .r3 .r3 8, .load .d .r17 .r3 0, .load .d .r10 .r3 8,
    .load .d .r12 .r3 16, .load .d .r0 .r3 24,
    .lsl .r0 .r0 63, .lsr .d .r15 .r12 1, .add .r15 .r15 .r0,
    .lsl .r12 .r12 63, .lsr .d .r16 .r10 1, .add .r16 .r16 .r12,
    .lsl .r10 .r10 63, .lsr .d .r17 .r17 1, .add .r17 .r17 .r10, .store .d .r17 .r9 40,
    .store .d .r16 .r9 48, .store .d .r15 .r9 56, .addi .r14 .r9 40, .li .r6 1, .load .d .r7 .r9 8,
    .load .d .r18 .r9 16, .sub .r22 .r7 .r15, .li .r20 0]

/-- A word of a number shifted right by one: `x`'s high bits and `y`'s low one. -/
abbrev f1 (x y : BitVec 64) : BitVec 64 := x >>> 1 + y <<< 63

theorem f1_val (x y : BitVec 64) : (f1 x y).toNat = (y.toNat * 2 ^ 64 + x.toNat) / 2 % 2 ^ 64 := by
  have := VG.Proof.Rsa.PPC64LE.RdShift.funnel_val x y (c := 1) (by decide) (by decide)
  simp only [f1]
  rw [this]
  have := x.isLt
  omega_using []

/-- A word of half a number: word `i` of `⌊V / 2⌋` is `f1` of `V`'s words `i` and `i + 1`. -/
theorem word_half (m : Mem) (B : Addr) {d n i : Nat} (hi : i + 2 ≤ n) :
    (f1 (Mont.word m B (d + 8 * i)) (Mont.word m B (d + 8 * (i + 1)))).toNat =
      wordsVal m B d n / 2 / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [f1_val, Nat.div_div_eq_div_mul, Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
    VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_div (show i ≤ n by omega_using [hi]),
    show n - i = (n - i - 2) + 1 + 1 by omega_using [hi], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low,
    VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []]
  generalize (Mont.word m B (d + 8 * i)).toNat = x
  generalize (Mont.word m B (d + 8 * (i + 1))).toNat = y
  generalize wordsVal m B (d + 8 * (i + 1) + 8) (n - i - 2) = z
  rw [show x + 2 ^ 64 * (y + 2 ^ 64 * z) = (y * 2 ^ 64 + x) + 2 * (2 ^ 63 * 2 ^ 64 * z) by
      rw [Nat.mul_add, show 2 ^ 64 * (2 ^ 64 * z) = 2 * (2 ^ 63 * 2 ^ 64 * z) by
        rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring]; omega_using [],
    Nat.add_mul_div_left _ _ (by decide), show 2 ^ 63 * 2 ^ 64 * z = (2 ^ 63 * z) * 2 ^ 64 by ring,
    Nat.add_mul_mod_self_right]


theorem estMid_raw {s : State} {B : Addr} {Z h j dT dS dM : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dT) (h9 : s.gpr .r9 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * h))
    (h24 : s.gpr .r24 = off B dS) (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj1 : 1 ≤ j) (hh : 2 ≤ h)
    (hh' : h < 2 ^ 20) (hT : dT + 8 * (j + 3) ≤ Z) (hS : dS + 8 * h ≤ Z) (hM : dM + 64 ≤ Z)
    (dTM : dT + 8 * (j + 3) ≤ dM ∨ dM + 64 ≤ dT) (dSM : dS + 8 * h ≤ dM ∨ dM + 64 ≤ dS) :
    WP isa (.block estMid) s fun t =>
      let T := fun i => Mont.word s.mem B (dT + 8 * i)
      (t.gpr .r15 = f1 (T (j + 1)) (T (j + 2)) ∧ t.gpr .r16 = f1 (T j) (T (j + 1)) ∧
        t.gpr .r7 = Mont.word s.mem B (dM + 8) ∧ t.gpr .r18 = Mont.word s.mem B (dM + 16) ∧
        t.gpr .r22 = Mont.word s.mem B (dM + 8) - f1 (T (j + 1)) (T (j + 2)) ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
        t.gpr .r6 = BitVec.ofNat 64 1 ∧ t.gpr .r14 = off B (dM + 40) ∧
        t.mem = (((s.mem.writeW (off B (dM + 24)) (f1 (Mont.word s.mem B (dS + 8 * (h - 2)))
          (Mont.word s.mem B (dS + 8 * (h - 1))))).writeW (off B (dM + 40)) (f1 (T (j - 1)) (T j))).writeW
          (off B (dM + 48)) (f1 (T j) (T (j + 1)))).writeW (off B (dM + 56)) (f1 (T (j + 1)) (T (j + 2)))) ∧
      Keep [.r0, .r3, .r6, .r7, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22] s t := by
  have hnw := hs.nowrap
  have eS : BitVec.ofNat 64 (2 * h) <<< 2 + off B dS - 16#64 = off B (dS + 8 * (h - 2)) := by
    rw [show BitVec.ofNat 64 (2 * h) <<< 2 = BitVec.ofNat 64 (8 * h) by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]; omega,
      BitVec.add_comm, off_add, show (16#64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega)]
    congr 1; omega
  have eT : BitVec.ofNat 64 j <<< 3 + off B dT - 8#64 = off B (dT + 8 * (j - 1)) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.shl3_val, BitVec.add_comm, off_add, show (8#64) = BitVec.ofNat 64 8 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega)]
    congr 1; omega
  have w1 : ∀ (a : BitVec 64) (d : Nat), d + 8 ≤ dM + 24 ∨ dM + 32 ≤ d → d + 8 ≤ Z →
      (s.mem.writeW (off B (dM + 24)) a).readW (off B d) 64 = Mont.word s.mem B d :=
    fun a d hd hdZ => (writeW_outside s.mem B (d := dM + 24) a (by omega)).word (by omega) (by omega)
  have w4 : ∀ (a b c e : BitVec 64) (d : Nat), d + 8 ≤ dM + 24 → (((((s.mem.writeW (off B (dM + 24)) a).writeW
      (off B (dM + 40)) b).writeW (off B (dM + 48)) c).writeW (off B (dM + 56)) e)).readW (off B d) 64 =
      Mont.word s.mem B d := fun a b c e d hd => by
    have o := ((((writeW_outside s.mem B (d := dM + 24) a (by omega)).mono (o' := dM + 24) (n' := 40) (by omega)
      (by omega)).trans ((writeW_outside _ B (d := dM + 40) b (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B (d := dM + 48) c (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B (d := dM + 56) e (by omega)).mono (by omega) (by omega))
    exact o.word (by omega) (by omega)
  refine WP.keep _ ?_ (by decide)
  mcrun [h5, h9, h11, h24, h26, eS, eT,
    w1 _ (dT + 8 * (j - 1)) (by omega) (by omega), w1 _ (dT + 8 * (j - 1) + 8) (by omega) (by omega),
    w1 _ (dT + 8 * (j - 1) + 16) (by omega) (by omega), w1 _ (dT + 8 * (j - 1) + 24) (by omega) (by omega),
    w4 _ _ _ _ (dM + 8) (by omega), w4 _ _ _ _ (dM + 16) (by omega),
    hs.ld (show dS + 8 * (h - 2) + 8 ≤ Z by omega), hs.ld (show dS + 8 * (h - 2) + 8 + 8 ≤ Z by omega),
    hs.st (show dM + 24 + 8 ≤ Z by omega), hs.st (show dM + 40 + 8 ≤ Z by omega),
    hs.st (show dM + 48 + 8 ≤ Z by omega), hs.st (show dM + 56 + 8 ≤ Z by omega),
    hs.ld (show dM + 8 + 8 ≤ Z by omega), hs.ld (show dM + 16 + 8 ≤ Z by omega),
    hs.ld (show dT + 8 * (j - 1) + 8 ≤ Z by omega), hs.ld (show dT + 8 * (j - 1) + 8 + 8 ≤ Z by omega),
    hs.ld (show dT + 8 * (j - 1) + 16 + 8 ≤ Z by omega), hs.ld (show dT + 8 * (j - 1) + 24 + 8 ≤ Z by omega)]
  simp only [f1, show dT + 8 * (j - 1) + 8 = dT + 8 * j by omega, show dT + 8 * (j - 1) + 16 = dT + 8 * (j + 1) by omega,
    show dT + 8 * (j - 1) + 24 = dT + 8 * (j + 2) by omega, show dS + 8 * (h - 2) + 8 = dS + 8 * (h - 1) by omega]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl | exact ⟨trivial, trivial⟩

theorem wordsVal_four (m : Mem) (B : Addr) (d : Nat) :
    wordsVal m B d 4 = (Mont.word m B d).toNat + 2 ^ 64 * ((Mont.word m B (d + 8)).toNat +
      2 ^ 64 * ((Mont.word m B (d + 16)).toNat + 2 ^ 64 * (Mont.word m B (d + 24)).toNat)) := by
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]

/-- The estimate at step `j` (`1 ≤ j < h`, `h ≥ 2`): from `⌊T / 2⌋`'s words `j - 1 … j + 1` (`U`, of the window `T`
at `dT`), `s₁` (from `D`'s words `h - 2`, `h - 1`) and `s₀ ≥ 2^63` with its reciprocal in the temporary's
words 1 and 2, `q̂ := min(⌊U / (s₀ β + s₁)⌋, β - 1)`, given `quot3`'s bounds on `quot`'s 2-by-1 estimate. -/
theorem estimate_ok {s : State} {B : Addr} {Z w N h j dX dS dT : Nat} (hW : Ws s B Z w N) (hN : 3 < N)
    (hw : w = 4 * h + 6) (hh2 : 2 ≤ h) (hh : h < 2 ^ 20)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 j) (hj1 : 1 ≤ j) (hj : j < h)
    (h19 : s.gpr .r19 = off B dX) (h24 : s.gpr .r24 = off B dS)
    (hX : dX + 8 * (2 * h) ≤ Z) (hS : dS + 8 * (h + 1) ≤ Z)
    (dXM : dX + 8 * (2 * h) ≤ arr w 3 ∨ arr w 3 + S w ≤ dX) (dSM : dS + 8 * (h + 1) ≤ arr w 3 ∨ arr w 3 + S w ≤ dS)
    (hdT : dT = dX + 8 * (2 * h - 2 * j - 2))
    (hs0 : 2 ^ 63 ≤ (Mont.word s.mem B (arr w 3 + 8)).toNat)
    (hv : (Mont.word s.mem B (arr w 3 + 16)).toNat = (2 ^ 128 - 1) / (Mont.word s.mem B (arr w 3 + 8)).toNat - 2 ^ 64) :
    let T := fun i => Mont.word s.mem B (dT + 8 * i)
    let u2 := (f1 (T (j + 1)) (T (j + 2))).toNat
    let u1 := (f1 (T j) (T (j + 1))).toNat
    let U := u2 * 2 ^ 128 + u1 * 2 ^ 64 + (f1 (T (j - 1)) (T j)).toNat
    let s0 := (Mont.word s.mem B (arr w 3 + 8)).toNat
    let Dd := s0 * 2 ^ 64 + (f1 (Mont.word s.mem B (dS + 8 * (h - 2))) (Mont.word s.mem B (dS + 8 * (h - 1)))).toNat
    u2 ≤ s0 → U < (2 ^ 64 + 1) * Dd → min (U / Dd) (2 ^ 64 - 1) ≤ min ((u2 * 2 ^ 64 + u1) / s0) (2 ^ 64 - 1) →
    min ((u2 * 2 ^ 64 + u1) / s0) (2 ^ 64 - 1) ≤ min (U / Dd) (2 ^ 64 - 1) + 2 →
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.estimate) s fun t =>
      ((t.gpr .r18).toNat = min (U / Dd) (2 ^ 64 - 1) ∧ Outside B (arr w 3 + 24) 40 s.mem t.mem) ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22] s t := by
  intro T u2 u1 U s0 Dd hu hUD hge hle
  have hs := hW.scr
  have hnw := hs.nowrap
  have fM := hW.arr_fit (j := 3) hN
  simp only [S] at fM dXM dSM
  rw [show VG.Impl.Rsa.PPC64LE.RecoverDet.estimate = (VG.Impl.Rsa.PPC64LE.RecoverDet.twoH ++
      VG.Impl.Rsa.PPC64LE.RecoverDet.ptrs) ++ (VG.Impl.Rsa.PPC64LE.Keys.ptr .r9 3 ++ (estMid ++
      ((quotMG ++ quotFix) ++ quot3))) from rfl, WP.block_append_iff]
  refine WP.mono (hp_ok hW.r29 hw hh h26 hj h19 h24) fun s1 ⟨⟨p11, p5, _, pm⟩, pk⟩ => ?_
  rw [← hdT] at p5
  have hW1 := hW.of_keep pk
  refine ptr_ok hW1 (r := .r9) (by decide) (by decide) (by decide) (show 3 < 2 ^ 15 by decide) ?_
  generalize hs2 : s1.write .r9 (off B (arr w 3)) = s2
  have k2 : Keep [.r9] s1 s2 := by rw [← hs2]; exact Keep.write _ _ _
  have q9 : s2.gpr .r9 = off B (arr w 3) := by rw [← hs2]; simp [gpr_write]
  have m2 : s2.mem = s.mem := by rw [← hs2, ← pm]; rfl
  have hs2' := hs.congr (pk.trans k2).wr
  have g : ∀ r, r ∉ [Reg.r5, .r6, .r11, .r9] → s2.gpr r = s.gpr r := fun r hr =>
    ((pk.trans k2).mono (rs' := [Reg.r5, .r6, .r11, .r9]) (by decide)).gpr r hr
  rw [WP.block_append_iff]
  refine WP.mono (estMid_raw (dT := dT) (dS := dS) (dM := arr w 3) (h := h) (j := j) hs2'
    ((k2.gpr .r5 (by decide)).trans p5) q9 ((k2.gpr .r11 (by decide)).trans p11) (by rw [g .r24 (by decide), h24])
    (by rw [g .r26 (by decide), h26]) hj1 hh2 hh (by omega_using [hj1, hj, hX, hdT]) (by omega_using [hS]) (by omega_using [hw, hh2, fM]) (by omega_using [hw, hj1, hj, dXM, hdT]) (by omega_using [hw, hh2, dSM]))
    fun s3 ⟨⟨a15, a16, a7, a18, a22, a20, a6, a14, am⟩, ak⟩ => ?_
  rw [m2] at a15 a16 a7 a18 a22 am
  have hs3 := hs2'.congr ak.wr
  -- The temporary's words after the middle.
  have ow : ∀ (a b c e : BitVec 64), Outside B (arr w 3 + 24) 40 s.mem (((((s.mem.writeW (off B (arr w 3 + 24)) a).writeW
      (off B (arr w 3 + 40)) b).writeW (off B (arr w 3 + 48)) c).writeW (off B (arr w 3 + 56)) e)) := fun a b c e =>
    ((((writeW_outside s.mem B (d := arr w 3 + 24) a (by omega_using [hw, hnw, fM])).mono (o' := arr w 3 + 24) (n' := 40) (by omega_using [])
      (by omega_using [])).trans ((writeW_outside _ B (d := arr w 3 + 40) b (by omega_using [hw, hh2, hnw, fM])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B (d := arr w 3 + 48) c (by omega_using [hw, hh2, hnw, fM])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B (d := arr w 3 + 56) e (by omega_using [hw, hh2, hnw, fM])).mono (by omega_using []) (by omega_using []))
  have o3 : Outside B (arr w 3 + 24) 40 s.mem s3.mem := by rw [am]; exact ow _ _ _ _
  have w24 : Mont.word s3.mem B (arr w 3 + 24) =
      f1 (Mont.word s.mem B (dS + 8 * (h - 2))) (Mont.word s.mem B (dS + 8 * (h - 1))) := by
    rw [am, (writeW_outside _ B (d := arr w 3 + 56) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hnw, fM]),
      (writeW_outside _ B (d := arr w 3 + 48) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hnw, fM]),
      (writeW_outside _ B (d := arr w 3 + 40) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hnw, fM]), word_writeW_self]
  have w40 : Mont.word s3.mem B (arr w 3 + 40) = f1 (T (j - 1)) (T j) := by
    rw [am, (writeW_outside _ B (d := arr w 3 + 56) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hh2, hnw, fM]),
      (writeW_outside _ B (d := arr w 3 + 48) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hh2, hnw, fM]), word_writeW_self]
  have w48 : Mont.word s3.mem B (arr w 3 + 48) = f1 (T j) (T (j + 1)) := by
    rw [am, (writeW_outside _ B (d := arr w 3 + 56) _ (by omega_using [hw, hh2, hnw, fM])).word (by omega_using []) (by omega_using [hw, hh2, hnw, fM]), word_writeW_self]
  have w56 : Mont.word s3.mem B (arr w 3 + 56) = f1 (T (j + 1)) (T (j + 2)) := by
    rw [am, word_writeW_self]
  have eW : wordsVal s3.mem B (arr w 3 + 32) 4 = (Mont.word s3.mem B (arr w 3 + 32)).toNat + 2 ^ 64 * U := by
    rw [wordsVal_four, show arr w 3 + 32 + 8 = arr w 3 + 40 by omega_using [], show arr w 3 + 32 + 16 = arr w 3 + 48 by omega_using [],
      show arr w 3 + 32 + 24 = arr w 3 + 56 by omega_using [], w40, w48, w56]
    simp only [U, u1, u2]
    omega_using []
  -- The 2-by-1 estimate.
  rw [WP.block_append_iff]
  refine WP.mono (mgFix_ok (by rw [a7]; exact hs0) (by rw [a18, a7]; exact hv) a20 (by rw [a22, a7, a15])
    (by rw [a15, a7]; exact hu)) fun s4 ⟨⟨b18, bm⟩, bk⟩ => ?_
  rw [a15, a16, a7] at b18
  have hs4 := hs3.congr bk.wr
  have d0 : 0 < Dd := by simp only [Dd]; have := hs0; omega_using [hUD]
  have hx := (Mont.word s3.mem B (arr w 3 + 32)).isLt
  have red : ((Mont.word s3.mem B (arr w 3 + 32)).toNat + 2 ^ 64 * U) * 2 ^ 0 / 2 ^ (64 * (4 - 3)) = U := by
    rw [Nat.pow_zero, Nat.mul_one, show 64 * (4 - 3) = 64 from rfl, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt hx, Nat.zero_add]
  have red2 : ((Mont.word s3.mem B (arr w 3 + 32)).toNat + 2 ^ 64 * U) * 2 ^ 0 / 2 ^ (64 * (4 - 2)) =
      u2 * 2 ^ 64 + u1 := by
    rw [show 64 * (4 - 2) = 64 + 64 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 2 ^ (64 * (4 - 3)) = 2 ^ 64 from rfl] at *
    rw [red]
    have := (f1 (T (j - 1)) (T j)).isLt
    simp only [U]
    omega_using []
  refine WP.mono (quot3At_ok (dX := arr w 3 + 32) (dT := arr w 3) (w := 4) (z := 0) (D := Dd) hs4
    (by rw [bk.gpr .r14 (by decide), a14]) (by rw [bk.gpr .r9 (by decide), ak.gpr .r9 (by decide), q9])
    (by rw [bk.gpr .r20 (by decide), a20]) (by decide) (by decide) (by omega_using [hw, hh2, fM]) (by omega_using [hw, fM])
    (by rw [bk.gpr .r6 (by decide), a6]; rfl) (by decide)
    (by rw [bk.gpr .r15 (by decide), bk.gpr .r16 (by decide), a15, a16, bm, eW, red2])
    (by rw [bk.gpr .r7 (by decide), a7, bm, w24]) d0
    (by rw [bm, eW, red]; exact hUD) (by rw [bm, eW, b18, red]; exact hge) (by rw [bm, eW, b18, red]; exact hle))
    fun t ⟨⟨t18, tm⟩, tk⟩ => ⟨⟨?_, by rw [tm, bm]; exact o3⟩, ?_⟩
  · rw [t18, bm, eW, red]
  · exact ((((pk.trans k2).trans ak).trans bk).trans tk).mono (by decide)

end Estimate

/-! ## A step -/

section Step
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S)

/-- The estimate's `U` from the window's words: `⌊R / 2⌋ / 2^(64 (j - 1))`, for `R` (`j + 3` words) whose
half has three words above `j - 1`. -/
theorem est_u (m : Mem) (B : Addr) {dT j : Nat} (hj : 1 ≤ j)
    (hU : wordsVal m B dT (j + 3) / 2 / 2 ^ (64 * (j - 1)) < 2 ^ 64 * 2 ^ 64 * 2 ^ 64) :
    (f1 (Mont.word m B (dT + 8 * (j + 1))) (Mont.word m B (dT + 8 * (j + 2)))).toNat * 2 ^ 128 +
      (f1 (Mont.word m B (dT + 8 * j)) (Mont.word m B (dT + 8 * (j + 1)))).toNat * 2 ^ 64 +
      (f1 (Mont.word m B (dT + 8 * (j - 1))) (Mont.word m B (dT + 8 * j))).toNat =
      wordsVal m B dT (j + 3) / 2 / 2 ^ (64 * (j - 1)) := by
  have w0 := word_half m B (d := dT) (n := j + 3) (i := j - 1) (by omega_using [])
  have w1 := word_half m B (d := dT) (n := j + 3) (i := j) (by omega_using [])
  have w2 := word_half m B (d := dT) (n := j + 3) (i := j + 1) (by omega_using [])
  rw [show j - 1 + 1 = j by omega_using [hj]] at w0
  rw [w0, w1, w2, show 64 * j = 64 * (j - 1) + 64 by omega_using [hj], show 64 * (j + 1) = 64 * (j - 1) + 64 + 64 by omega_using [hj],
    Nat.pow_add, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  generalize wordsVal m B dT (j + 3) / 2 / 2 ^ (64 * (j - 1)) = Y at hU ⊢
  omega_using [hU]

/-- The estimate's `s₀ β + s₁` from `D = 2 s` (`j + 1` words at `h - j`, zero below), and the temporary's
`s₀`: `s β / 2^(64 (j - 1))`'s low word is `f1` of `D`'s words `h - 2` and `h - 1`. -/
theorem est_d (m : Mem) (B : Addr) {dS h j s : Nat} (hj : 1 ≤ j) (hjh : j < h)
    (hz : wordsVal m B dS (h - j) = 0) (hd : wordsVal m B (dS + 8 * (h - j)) (j + 1) = 2 * s) :
    (f1 (Mont.word m B (dS + 8 * (h - 2))) (Mont.word m B (dS + 8 * (h - 1)))).toNat =
      s * 2 ^ 64 / 2 ^ (64 * (j - 1)) % 2 ^ 64 := by
  have w := word_half m B (d := dS) (n := h + 1) (i := h - 2) (by omega_using [hjh])
  rw [show h - 2 + 1 = h - 1 by omega_using [hj, hjh]] at w
  rw [w, show h + 1 = (h - j) + (j + 1) by omega_using [hjh], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, hz, hd,
    Nat.zero_add, show 2 ^ (64 * (h - j)) * (2 * s) = 2 * (2 ^ (64 * (h - j)) * s) by ring,
    Nat.mul_div_cancel_left _ (by decide)]
  have e : 2 ^ (64 * (h - 2)) * 2 ^ 64 = 2 ^ (64 * (h - j)) * 2 ^ (64 * (j - 1)) := by
    rw [← Nat.pow_add, ← Nat.pow_add, show 64 * (h - 2) + 64 = 64 * (h - j) + 64 * (j - 1) by omega_using [hj, hjh]]
  rw [← Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64), e, Nat.mul_assoc,
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]


/-- Before step `j` (`1 ≤ j ≤ h`) of the root of `X` (`2 h` words, normalized): the root `s` of `X`'s top
`2 j` words (`j` words, its top one at least `2^63`), `X'` (`[wR]`) holding `X`'s low `2 h - 2 j` words and
the remainder (`j + 1` words) above them, `D` (`[wS]`) `2 s` in its top `j + 1` words and zero below,
and the temporary `s`'s top word and its reciprocal in words 1 and 2. -/
structure SqInv (t : State) (B : Addr) (Z w N h X s j : Nat) : Prop where
  ws : Ws t B Z w N
  hN : 18 < N
  hw : w = 4 * h + 6
  h2 : 2 ≤ h
  hh : h < 2 ^ 20
  j1 : 1 ≤ j
  jh : j ≤ h
  r19 : t.gpr .r19 = off B (arr w 18)
  r24 : t.gpr .r24 = off B (arr w 2)
  r26 : t.gpr .r26 = BitVec.ofNat 64 j
  r28 : t.gpr .r28 = BitVec.ofNat 64 (h - j)
  sq : s * s ≤ X / 2 ^ (64 * (2 * h - 2 * j))
  sr : X / 2 ^ (64 * (2 * h - 2 * j)) - s * s ≤ 2 * s
  sbig : 2 ^ 63 * 2 ^ (64 * (j - 1)) ≤ s
  slt : s < 2 ^ (64 * j)
  low : wordsVal t.mem B (arr w 18) (2 * h - 2 * j) = X % 2 ^ (64 * (2 * h - 2 * j))
  rem : wordsVal t.mem B (arr w 18 + 8 * (2 * h - 2 * j)) (j + 1) = X / 2 ^ (64 * (2 * h - 2 * j)) - s * s
  dv : wordsVal t.mem B (arr w 2 + 8 * (h - j)) (j + 1) = 2 * s
  dz : wordsVal t.mem B (arr w 2) (h - j) = 0
  t1 : (Mont.word t.mem B (arr w 3 + 8)).toNat = s / 2 ^ (64 * (j - 1))
  t2 : (Mont.word t.mem B (arr w 3 + 16)).toNat = (2 ^ 128 - 1) / (Mont.word t.mem B (arr w 3 + 8)).toNat - 2 ^ 64
  hi : wordsVal t.mem B (arr w 18 + 8 * (2 * h - j + 1)) (j - 1) = 0
  dhi : wordsVal t.mem B (arr w 2 + 8 * (h + 1)) (h + 2) = 0

/-- The sign bit of a window's top word, as the window's value. -/
theorem top_neg (m : Mem) (B : Addr) (d j : Nat) :
    (Mont.word m B (d + 8 * (j + 2))).toNat / 2 ^ 63 = wordsVal m B d (j + 3) / 2 ^ (64 * (j + 2) + 63) := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
    VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_div (show j + 2 ≤ j + 3 by omega_using []), show j + 3 - (j + 2) = 0 + 1 by omega_using [],
    VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low]
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero]

theorem neg_mul {n Q X : Nat} (hn : n ≤ 1) (hq : n = 1 → 1 ≤ Q) : n * (2 * Q - 1 + X) = n * (X + 2 * Q - 1) := by
  rcases (show n = 0 ∨ n = 1 by omega_using [hn]) with rfl | rfl
  · simp
  · have := hq rfl; omega_using [hq]

/-- The estimate's `U` from the window at `dT`. -/
def Um (m : Mem) (B : Addr) (dT j : Nat) : Nat :=
  (f1 (Mont.word m B (dT + 8 * (j + 1))) (Mont.word m B (dT + 8 * (j + 2)))).toNat * 2 ^ 128 +
    (f1 (Mont.word m B (dT + 8 * j)) (Mont.word m B (dT + 8 * (j + 1)))).toNat * 2 ^ 64 +
    (f1 (Mont.word m B (dT + 8 * (j - 1))) (Mont.word m B (dT + 8 * j))).toNat

/-- `U`'s top two words. -/
def U21 (m : Mem) (B : Addr) (dT j : Nat) : Nat :=
  (f1 (Mont.word m B (dT + 8 * (j + 1))) (Mont.word m B (dT + 8 * (j + 2)))).toNat * 2 ^ 64 +
    (f1 (Mont.word m B (dT + 8 * j)) (Mont.word m B (dT + 8 * (j + 1)))).toNat

/-- The estimate's `s₀ β + s₁`, from the temporary (at `dM`) and `D` (at `dS`). -/
def Ddm (m : Mem) (B : Addr) (dM dS h : Nat) : Nat :=
  (Mont.word m B (dM + 8)).toNat * 2 ^ 64 +
    (f1 (Mont.word m B (dS + 8 * (h - 2))) (Mont.word m B (dS + 8 * (h - 1)))).toNat

/-- A step's numbers, from the invariant's memory: the window `R`, the digit `q`, the next root and
remainder, and the estimate's conditions and bounds. -/
theorem step_pre {m : Mem} {B : Addr} {w h j X s dT : Nat} (j1 : 1 ≤ j) (hj : j < h)
    (hdT : dT = arr w 18 + 8 * (2 * h - 2 * j - 2))
    (sq : s * s ≤ X / 2 ^ (64 * (2 * h - 2 * j))) (sr : X / 2 ^ (64 * (2 * h - 2 * j)) - s * s ≤ 2 * s)
    (sbig : 2 ^ 63 * 2 ^ (64 * (j - 1)) ≤ s) (slt : s < 2 ^ (64 * j))
    (low : wordsVal m B (arr w 18) (2 * h - 2 * j) = X % 2 ^ (64 * (2 * h - 2 * j)))
    (rem : wordsVal m B (arr w 18 + 8 * (2 * h - 2 * j)) (j + 1) = X / 2 ^ (64 * (2 * h - 2 * j)) - s * s)
    (dv : wordsVal m B (arr w 2 + 8 * (h - j)) (j + 1) = 2 * s) (dz : wordsVal m B (arr w 2) (h - j) = 0)
    (t1 : (Mont.word m B (arr w 3 + 8)).toNat = s / 2 ^ (64 * (j - 1))) :
    ∃ R q, wordsVal m B dT (j + 3) = R ∧ IsDigit (2 ^ 64) s R q ∧
      (s * 2 ^ 64 + q) * (s * 2 ^ 64 + q) + (R - (2 * s * 2 ^ 64 + q) * q) = X / 2 ^ (64 * (2 * h - 2 * j - 2)) ∧
      R - (2 * s * 2 ^ 64 + q) * q ≤ 2 * (s * 2 ^ 64 + q) ∧ q < 2 ^ 64 ∧
      wordsVal m B (arr w 18) (2 * h - 2 * j - 2) = X % 2 ^ (64 * (2 * h - 2 * j - 2)) ∧
      R < 2 ^ (64 * (j + 2) + 63) ∧ (2 * s * 2 ^ 64 + (q + 2)) * (q + 2) ≤ R + 2 ^ (64 * (j + 2) + 63) ∧
      (f1 (Mont.word m B (dT + 8 * (j + 1))) (Mont.word m B (dT + 8 * (j + 2)))).toNat ≤
        (Mont.word m B (arr w 3 + 8)).toNat ∧
      Um m B dT j < (2 ^ 64 + 1) * Ddm m B (arr w 3) (arr w 2) h ∧
      min (Um m B dT j / Ddm m B (arr w 3) (arr w 2) h) (2 ^ 64 - 1) ≤
        min (U21 m B dT j / (Mont.word m B (arr w 3 + 8)).toNat) (2 ^ 64 - 1) ∧
      min (U21 m B dT j / (Mont.word m B (arr w 3 + 8)).toNat) (2 ^ 64 - 1) ≤
        min (Um m B dT j / Ddm m B (arr w 3) (arr w 2) h) (2 ^ 64 - 1) + 2 ∧
      q ≤ min (Um m B dT j / Ddm m B (arr w 3) (arr w 2) h) (2 ^ 64 - 1) ∧
      min (Um m B dT j / Ddm m B (arr w 3) (arr w 2) h) (2 ^ 64 - 1) ≤ q + 2 := by
  obtain ⟨E, hE⟩ : ∃ E, E = 2 ^ (64 * (2 * h - 2 * j - 2)) := ⟨_, rfl⟩
  have eE : 2 ^ (64 * (2 * h - 2 * j)) = E * (2 ^ 64 * 2 ^ 64) := by
    rw [hE, ← Nat.pow_add, ← Nat.pow_add, show 64 * (2 * h - 2 * j - 2) + (64 + 64) =
      64 * (2 * h - 2 * j) by omega_using [hj]]
  rw [eE] at sq sr low rem
  obtain ⟨A, hA⟩ : ∃ A, A = X / (E * (2 ^ 64 * 2 ^ 64)) := ⟨_, rfl⟩
  rw [← hA] at sq sr rem
  obtain ⟨r, hr⟩ : ∃ r, r = A - s * s := ⟨_, rfl⟩
  rw [← hr] at sr rem
  obtain ⟨P, hP⟩ : ∃ P, P = X / E % (2 ^ 64 * 2 ^ 64) := ⟨_, rfl⟩
  have hPlt : P < 2 ^ 64 * 2 ^ 64 := by rw [hP]; exact Nat.mod_lt _ (by decide)
  have hXE : X / E = A * (2 ^ 64 * 2 ^ 64) + P := by
    rw [hA, hP, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
  have hEpos : 0 < E := by rw [hE]; exact Nat.two_pow_pos _
  have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append m B (arr w 18) (2 * h - 2 * j - 2) 2
  rw [show 2 * h - 2 * j - 2 + 2 = 2 * h - 2 * j by omega_using [hj], low, ← hdT] at sp
  have hlo := wordsVal_lt m B (arr w 18) (2 * h - 2 * j - 2)
  rw [← hE] at sp hlo
  have hRw : wordsVal m B dT (j + 3) = r * (2 ^ 64 * 2 ^ 64) + P := by
    have e2 : wordsVal m B dT 2 = P := by
      rw [hP, ← Nat.mod_mul_right_div_self, sp, Nat.add_mul_div_left _ _ hEpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
    rw [show j + 3 = 2 + (j + 1) by omega_using [], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, e2,
      show dT + 8 * 2 = arr w 18 + 8 * (2 * h - 2 * j) by omega_using [hj, hdT], rem]
    ring
  have low' : wordsVal m B (arr w 18) (2 * h - 2 * j - 2) = X % E := by
    have := congrArg (· % E) sp
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.mod_mul_right_mod] at this
    exact this.symm
  obtain ⟨q, hq⟩ := digit_exists (2 ^ 64) s (r * (2 ^ 64 * 2 ^ 64) + P)
  have hs0 : 2 ^ 63 ≤ s / 2 ^ (64 * (j - 1)) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr sbig
  have hqβ : q < 2 ^ 64 := VG.Proof.Bignum.SqrtRem.digit_lt sr hPlt hq.1
  obtain ⟨eb1, eb2, eb3, eb4, eb5⟩ := est_bounds hs0 sr hPlt hq
  obtain ⟨sb1, sb2, sb3, sb4⟩ := step_bounds j1 slt sr hPlt hqβ
  obtain ⟨si1, si2⟩ := VG.Proof.Bignum.SqrtRem.step_inv (A := A) (by omega_using [sbig, slt, t1, sq, hA, sr, hr, hXE, hs0, eb1, eb2, eb3, eb4, eb5, sb1, sb2, sb3, sb4]) hq
  have eU := est_u m B (dT := dT) j1 (by rw [hRw]; exact sb4)
  rw [hRw] at eU
  have eS1 := est_d m B (dS := arr w 2) (s := s) j1 hj dz dv
  have eSK : s * 2 ^ 64 / 2 ^ (64 * (j - 1)) / 2 ^ 64 = s / 2 ^ (64 * (j - 1)) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64)]
  have hu0 := (f1 (Mont.word m B (dT + 8 * (j - 1))) (Mont.word m B (dT + 8 * j))).isLt
  have hu1 := (f1 (Mont.word m B (dT + 8 * j)) (Mont.word m B (dT + 8 * (j + 1)))).isLt
  have hDe : Ddm m B (arr w 3) (arr w 2) h = s * 2 ^ 64 / 2 ^ (64 * (j - 1)) := by
    unfold Ddm; rw [t1, eS1, ← eSK]; exact Nat.div_add_mod' _ _
  have hDs : s * 2 ^ 64 / 2 ^ (64 * (j - 1)) / 2 ^ 64 = (Mont.word m B (arr w 3 + 8)).toNat := by rw [eSK, t1]
  have eUm : Um m B dT j = (r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) := eU
  have eY : (r * (2 ^ 64 * 2 ^ 64) + P) / 2 / 2 ^ (64 * (j - 1)) / 2 ^ 64 = U21 m B dT j := by
    unfold U21; rw [← eU]; omega_using []
  refine ⟨_, q, hRw, hq, ?_, si2, hqβ, by rw [low', hE], sb1, sb2, ?_, by rw [eUm, hDe]; exact eb1,
    by rw [eUm, hDe, ← eY, ← hDs]; exact eb2, by rw [eUm, hDe, ← eY, ← hDs]; exact eb3,
    by rw [eUm, hDe]; exact eb4, by rw [eUm, hDe]; exact eb5⟩
  · rw [← hE, hXE, ← si1]
  · rw [t1]; rw [← eU] at sb3; omega_using [sbig, slt, t1, sq, sr, hs0, eb1, eb2, eb3, eb4, eb5, sb2, sb3, sb4, si1, si2, eU, eS1, eSK, hDs]

/-- A step after its estimate: the multiply-and-subtract, two corrections and `D := 2 s'`, from `q̂` within 2
above the digit `q` of the window `R` (`dT`) after the root `s` (`2 s` in `D`'s words above `dD`). -/
theorem step_corr {v : State} {B : Addr} {Z w h j dT dD s R q : Nat} (hs : Scr v B Z)
    (h29 : v.gpr .r29 = BitVec.ofNat 64 w) (hw : w = 4 * h + 6) (hh : h < 2 ^ 20)
    (h26 : v.gpr .r26 = BitVec.ofNat 64 j) (j1 : 1 ≤ j) (hj : j < h)
    (h19 : v.gpr .r19 = off B (arr w 18)) (h24 : v.gpr .r24 = off B (arr w 2))
    (hX : arr w 18 + 8 * (2 * h) ≤ Z) (hS : arr w 2 + 8 * (h + 1) ≤ Z)
    (dXS : arr w 2 + 8 * (h + 1) ≤ arr w 18)
    (hdT : dT = arr w 18 + 8 * (2 * h - 2 * j - 2)) (hdD : dD = arr w 2 + 8 * (h - 1 - j))
    (hR : wordsVal v.mem B dT (j + 3) = R) (hD : wordsVal v.mem B (dD + 8) (j + 1) = 2 * s)
    (hq : IsDigit (2 ^ 64) s R q) (sb1 : R < 2 ^ (64 * (j + 2) + 63))
    (sb2 : (2 * s * 2 ^ 64 + (q + 2)) * (q + 2) ≤ R + 2 ^ (64 * (j + 2) + 63))
    (hQ1 : q ≤ (v.gpr .r18).toNat) (hQ2 : (v.gpr .r18).toNat ≤ q + 2) :
    WP isa (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.mulSubD (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.correct
      (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.correct (.block VG.Impl.Rsa.PPC64LE.RecoverDet.finishQ)))) v fun t =>
      wordsVal t.mem B dT (j + 3) = R - (2 * s * 2 ^ 64 + q) * q ∧
      wordsVal t.mem B dD (j + 2) = 2 * (s * 2 ^ 64 + q) ∧
      (∀ d k, d + 8 * k ≤ Z → (d + 8 * k ≤ dT ∨ dT + 8 * (j + 3) ≤ d) → (d + 8 * k ≤ dD ∨ dD + 16 ≤ d) →
        wordsVal t.mem B d k = wordsVal v.mem B d k) ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2] [] v.mem t.mem ∧
      t.gpr .r26 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r28 = v.gpr .r28 - BitVec.ofNat 64 1 ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r17, .r18, .r20, .r22, .r26, .r28] v t := by
  have hnw := hs.nowrap
  refine WP.seq (WP.mono (mulSubD_ok (dX := arr w 18) (dS := arr w 2) (dT := dT) (dD := dD) hs h29 hw hh h26 j1 hj
    h19 h24 hX hS (by omega_arith) hdT hdD) fun v2 ⟨⟨b1, hb1, m1v⟩, mout, m20, mk⟩ => ?_)
  have mQ : wordsVal (v.mem.writeW (off B dD) (v.gpr .r18)) B dD (j + 2) = (v.gpr .r18).toNat + 2 ^ 64 * (2 * s) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, word_writeW_self,
      (writeW_outside v.mem B (d := dD) _ (by omega_arith)).wordsVal (d := dD + 8) (k := j + 1) (by omega_arith) (by omega_arith), hD]
  rw [hR, mQ] at m1v
  have eM : 2 ^ (64 * (j + 3)) = 2 * 2 ^ (64 * (j + 2) + 63) := by
    rw [show 64 * (j + 3) = (64 * (j + 2) + 63) + 1 by omega_using [], Nat.pow_succ, Nat.mul_comm]
  have h1 : wordsVal v2.mem B dT (j + 3) + (2 * s * 2 ^ 64 + (v.gpr .r18).toNat) * (v.gpr .r18).toNat +
      2 * 2 ^ (64 * (j + 2) + 63) * b1 = R + 2 * 2 ^ (64 * (j + 2) + 63) := by
    rw [← eM, ← m1v]; ring
  have hW1 := wordsVal_lt v2.mem B dT (j + 3)
  rw [eM] at hW1
  have hs2 := hs.congr mk.wr
  have mD2 : wordsVal v2.mem B (dD + 8) (j + 1) = 2 * s := by
    rw [mout.wordsVal (by omega_arith) (by omega_arith), (writeW_outside v.mem B (d := dD) _ (by omega_arith)).wordsVal (by omega_arith)
      (by omega_arith), hD]
  have hev : ∀ m : Mem, wordsVal m B (dD + 8) (j + 1) = 2 * s → (Mont.word m B (dD + 8)).toNat % 2 = 0 := by
    intro m hm
    rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low] at hm
    omega_using [hm]
  have c1q := corr1 sb1 h1 hb1 hW1
  refine WP.seq (WP.mono (correct_ok (dX := arr w 18) (dS := arr w 2) (dT := dT) (dD := dD) hs2
    ((mk.gpr .r29 (by decide)).trans h29) hw hh ((mk.gpr .r26 (by decide)).trans h26) j1 hj
    ((mk.gpr .r19 (by decide)).trans h19) ((mk.gpr .r24 (by decide)).trans h24) hX hS (by omega_arith)
    hdT hdD (by rw [top_neg, mk.gpr .r18 (by decide)]; exact c1q) (hev _ mD2))
    fun v3 ⟨⟨c2, hc2, c2v⟩, q18, q20, qout, qk⟩ => ?_)
  rw [top_neg] at c2v q18
  rw [mD2] at c2v
  rw [mk.gpr .r18 (by decide)] at c2v q18
  have hn1 : wordsVal v2.mem B dT (j + 3) / 2 ^ (64 * (j + 2) + 63) ≤ 1 :=
    Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega_arith))
  rw [neg_mul hn1 c1q, Nat.mul_comm (2 ^ 64) (2 * s), eM] at c2v
  have hW2 := wordsVal_lt v3.mem B dT (j + 3)
  rw [eM] at hW2
  have c2q := corr2 sb1 hq.1 hq.2 hQ1 hQ2 sb2 h1 hb1 hW1 c2v hc2 hW2
  have hs3 := hs2.congr qk.wr
  have mD3 : wordsVal v3.mem B (dD + 8) (j + 1) = 2 * s := by
    rw [qout.wordsVal (by omega_arith) (by omega_arith), mD2]
  have k3 := mk.trans qk
  refine WP.seq (WP.mono (correct_ok (dX := arr w 18) (dS := arr w 2) (dT := dT) (dD := dD) hs3
    ((k3.gpr .r29 (by decide)).trans h29) hw hh ((k3.gpr .r26 (by decide)).trans h26) j1 hj
    ((k3.gpr .r19 (by decide)).trans h19) ((k3.gpr .r24 (by decide)).trans h24) hX hS (by omega_arith)
    hdT hdD (by rw [top_neg, q18]; exact c2q) (hev _ mD3))
    fun v4 ⟨⟨c3, hc3, c3v⟩, p18, p20, pout, pk⟩ => ?_)
  rw [top_neg] at c3v p18
  rw [mD3] at c3v
  have hn2 : wordsVal v3.mem B dT (j + 3) / 2 ^ (64 * (j + 2) + 63) ≤ 1 :=
    Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega_arith))
  rw [q18] at c3v p18
  rw [neg_mul hn2 c2q, Nat.mul_comm (2 ^ 64) (2 * s), eM] at c3v
  have hW3 := wordsVal_lt v4.mem B dT (j + 3)
  rw [eM] at hW3
  obtain ⟨-, -, fq, fw⟩ := corr_chain sb1 hq.1 hq.2 hQ1 hQ2 sb2 h1 hb1 hW1 c2v hc2 hW2 c3v hc3 hW3
  rw [fq] at p18
  have hs4 := hs3.congr pk.wr
  have k4 := k3.trans pk
  have mD4 : wordsVal v4.mem B (dD + 8) (j + 1) = 2 * s := by
    rw [pout.wordsVal (by omega_arith) (by omega_arith), mD3]
  refine WP.mono (finishQ_ok (dX := arr w 18) (dS := arr w 2) (dD := dD) hs4 ((k4.gpr .r29 (by decide)).trans h29)
    hw hh ((k4.gpr .r26 (by decide)).trans h26) hj ((k4.gpr .r19 (by decide)).trans h19)
    ((k4.gpr .r24 (by decide)).trans h24) hS hdD (hev _ mD4))
    fun v5 ⟨f2, _, fout, f26, f28, fk⟩ => ⟨?_, ?_, ?_, ?_, f26, ?_, (k4.trans fk).mono (by decide)⟩
  · rw [fout.wordsVal (by omega_arith) (by omega_arith), fw]
  · rw [p18] at f2
    rw [show j + 2 = 2 + j by omega_using [], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, f2,
      fout.wordsVal (d := dD + 8 * 2) (by omega_arith) (by omega_arith)]
    rw [VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, show dD + 8 + 8 = dD + 8 * 2 by omega_using []] at mD4
    omega_using [mD4]
  · intro d k hdk h1' h2'
    rw [fout.wordsVal (by omega_arith) (by omega_arith), pout.wordsVal (by omega_arith) (by omega_arith), qout.wordsVal (by omega_arith) (by omega_arith),
      mout.wordsVal (by omega_arith) (by omega_arith), (writeW_outside v.mem B (d := dD) _ (by omega_arith)).wordsVal (by omega_arith)
      (by omega_arith)]
  · have kT : ∀ {m m' : Mem}, Outside B dT (8 * (j + 3)) m m' → VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2] [] m m' :=
      fun ho => VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 18) (d := 8 * (2 * h - 2 * j - 2)) (by rw [← hdT]; exact ho)
        (by simp only [S]; omega_arith) (by simp)
    have kD : ∀ {m m' : Mem} {n : Nat}, n ≤ 16 → Outside B dD n m m' →
        VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2] [] m m' :=
      fun hn ho => VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 2) (d := 8 * (h - 1 - j)) (by rw [← hdD]; exact ho)
        (by simp only [S]; omega_arith) (by simp)
    exact ((((kD (by decide) (writeW_outside v.mem B (d := dD) (v.gpr .r18) (by omega_arith))).trans (kT mout)).trans
      (kT qout)).trans (kT pout)).trans (kD (Nat.le_refl _) fout)
  · rw [f28, k4.gpr .r28 (by decide)]

/-- A step, `j < h`: the next digit. -/
theorem step_ok {t : State} {B : Addr} {Z w N h X s j : Nat} (I : SqInv t B Z w N h X s j) (hj : j < h) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.sqStep t fun t' =>
      (∃ s', SqInv t' B Z w N h X s' (j + 1)) ∧ t'.gpr .r28 = t.gpr .r28 - BitVec.ofNat 64 1 ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] t.mem t'.mem ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22, .r26,
        .r28] t t' := by
  obtain ⟨hW, hN, hw, h2, hh, j1, jh, r19, r24, r26, r28, sq, sr, sbig, slt, low, rem, dv, dz, t1, t2, hi, dhi⟩ := I
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  have f2 := hW.arr_fit (j := 2) (by omega_using [hN])
  have f3 := hW.arr_fit (j := 3) (by omega_using [hN])
  have a23 : arr w 2 + S w ≤ arr w 3 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  have a318 : arr w 3 + S w ≤ arr w 18 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  simp only [S] at f18 f2 f3 a23 a318
  obtain ⟨dT, hdT⟩ : ∃ dT, dT = arr w 18 + 8 * (2 * h - 2 * j - 2) := ⟨_, rfl⟩
  obtain ⟨dD, hdD⟩ : ∃ dD, dD = arr w 2 + 8 * (h - 1 - j) := ⟨_, rfl⟩
  obtain ⟨R, q, hR, hq, si1, si2, hqβ, low', sb1, sb2, hu2, hUD, hge, hle, hQ1, hQ2⟩ :=
    step_pre (m := t.mem) j1 hj hdT sq sr sbig slt low rem dv dz t1
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.sqStep
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.mono (estimate_ok (s := t) (dX := arr w 18) (dS := arr w 2) (dT := dT) (j := j) hW (by omega_using [hN])
    hw h2 hh r26 j1 hj r19 r24 (by omega_arith) (by omega_arith) (by simp only [S]; omega_arith)
    (by simp only [S]; omega_arith) hdT (by rw [t1]; exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr sbig)
    t2 hu2 hUD hge hle) fun v1 ⟨⟨e18, eout⟩, ek⟩ => ?_)
  have e18' : (v1.gpr .r18).toNat = min (Um t.mem B dT j / Ddm t.mem B (arr w 3) (arr w 2) h) (2 ^ 64 - 1) := e18
  rw [← e18'] at hQ1 hQ2
  have hs1 := hs.congr ek.wr
  have mR : wordsVal v1.mem B dT (j + 3) = R := by rw [eout.wordsVal (by omega_arith) (by omega_arith), hR]
  have mD : wordsVal v1.mem B (dD + 8) (j + 1) = 2 * s := by
    rw [eout.wordsVal (by omega_arith) (by omega_arith), show dD + 8 = arr w 2 + 8 * (h - j) by omega_using [hj, hdD], dv]
  refine WP.mono (step_corr hs1 ((ek.gpr .r29 (by decide)).trans hW.r29) hw hh ((ek.gpr .r26 (by decide)).trans r26)
    j1 hj ((ek.gpr .r19 (by decide)).trans r19) ((ek.gpr .r24 (by decide)).trans r24) (by omega_arith) (by omega_arith)
    (by omega_arith) hdT hdD mR mD hq sb1 sb2 hQ1 hQ2)
    fun t' ⟨cw, cd, cfr, ckw, c26, c28, ck⟩ => ?_
  have kk := ek.trans ck
  have fr : ∀ d k, d + 8 * k ≤ Z → (d + 8 * k ≤ dT ∨ dT + 8 * (j + 3) ≤ d) → (d + 8 * k ≤ dD ∨ dD + 16 ≤ d) →
      (d + 8 * k ≤ arr w 3 + 24 ∨ arr w 3 + 24 + 40 ≤ d) → wordsVal t'.mem B d k = wordsVal t.mem B d k :=
    fun d k hz h1 h2 h3 => by rw [cfr d k hz h1 h2, eout.wordsVal h3 (by omega_arith)]
  have fw : ∀ d, d + 8 ≤ Z → (d + 8 ≤ dT ∨ dT + 8 * (j + 3) ≤ d) → (d + 8 ≤ dD ∨ dD + 16 ≤ d) →
      (d + 8 ≤ arr w 3 + 24 ∨ arr w 3 + 24 + 40 ≤ d) → Mont.word t'.mem B d = Mont.word t.mem B d :=
    fun d hz h1 h2 h3 => by
      have := fr d 1 hz h1 h2 h3
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
      exact BitVec.eq_of_toNat_eq this
  have eK : 2 ^ (64 * j) = 2 ^ (64 * (j - 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add, show 64 * (j - 1) + 64 = 64 * j by omega_using [j1]]
  have e2 : 2 * h - 2 * (j + 1) = 2 * h - 2 * j - 2 := by omega_using []
  have hs' : s * 2 ^ 64 + q < 2 ^ (64 * (j + 1)) := by
    rw [show 64 * (j + 1) = 64 * j + 64 by omega_using [], Nat.pow_add]
    have := Nat.mul_le_mul_right (2 ^ 64) (show s + 1 ≤ 2 ^ (64 * j) by omega_using [slt])
    rw [Nat.add_mul, Nat.one_mul] at this
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hqβ _) this
  have top0 : (Mont.word t'.mem B (dT + 8 * (j + 2))).toNat = 0 := by
    have top := VG.Proof.Mont.wordsVal_succ_top t'.mem B dT (j + 2)
    rw [show j + 2 + 1 = j + 3 by omega_using [], cw] at top
    have hlt : R - (2 * s * 2 ^ 64 + q) * q < 2 ^ (64 * (j + 2)) := by
      rw [show 64 * (j + 2) = 64 * (j + 1) + 64 by omega_using [], Nat.pow_add]
      refine Nat.lt_of_le_of_lt si2 (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hs' (by decide)) ?_)
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (by decide)
    rcases Nat.eq_zero_or_pos (Mont.word t'.mem B (dT + 8 * (j + 2))).toNat with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * (j + 2))) h0
      omega_arith
  refine ⟨⟨s * 2 ^ 64 + q, ?_⟩, ?_, ?_, kk.mono (by decide)⟩
  · refine ⟨hW.of_keep kk, hN, hw, h2, hh, by omega_using [], by omega_using [hj], (kk.gpr .r19 (by decide)).trans r19,
      (kk.gpr .r24 (by decide)).trans r24, c26, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [c28, ek.gpr .r28 (by decide), r28]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hj]
    · rw [e2, ← si1]; exact Nat.le_add_right _ _
    · rw [e2, ← si1, Nat.add_sub_cancel_left]; exact si2
    · rw [Nat.add_sub_cancel, eK]
      have := Nat.mul_le_mul_right (2 ^ 64) sbig
      rw [Nat.mul_assoc] at this
      exact Nat.le_trans this (Nat.le_add_right _ _)
    · exact hs'
    · rw [e2, fr _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), low']
    · rw [e2, ← hdT, ← si1, Nat.add_sub_cancel_left]
      have top := VG.Proof.Mont.wordsVal_succ_top t'.mem B dT (j + 2)
      rw [show j + 2 + 1 = j + 3 by omega_using [], cw] at top
      have hlt : R - (2 * s * 2 ^ 64 + q) * q < 2 ^ (64 * (j + 2)) := by
        rw [show 64 * (j + 2) = 64 * (j + 1) + 64 by omega_using [], Nat.pow_add]
        refine Nat.lt_of_le_of_lt si2 (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hs' (by decide)) ?_)
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by decide)
      rcases Nat.eq_zero_or_pos (Mont.word t'.mem B (dT + 8 * (j + 2))).toNat with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.add_zero] at top; exact top.symm
      · have := Nat.le_mul_of_pos_right (2 ^ (64 * (j + 2))) h0
        omega_arith
    · rw [show h - (j + 1) = h - 1 - j by omega_using [], ← hdD, cd]
    · rw [fr _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append t.mem B (arr w 2) (h - (j + 1)) 1
      rw [show h - (j + 1) + 1 = h - j by omega_using [hj], dz] at sp
      omega_using [sp]
    · rw [fw _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), t1, Nat.add_sub_cancel, eK,
        Nat.mul_comm (2 ^ (64 * (j - 1))) (2 ^ 64), ← Nat.div_div_eq_div_mul, Nat.mul_comm s,
        Nat.mul_add_div (Nat.two_pow_pos 64), Nat.div_eq_of_lt hqβ, Nat.add_zero]
    · rw [fw _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        fw (arr w 3 + 8) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), t2]
    · have e := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low t'.mem B (dT + 8 * (j + 2)) (j - 1)
      rw [show j - 1 + 1 = j by omega_using [j1], show dT + 8 * (j + 2) + 8 = arr w 18 + 8 * (2 * h - j + 1) by omega_using [hj, hdT],
        fr (arr w 18 + 8 * (2 * h - j + 1)) (j - 1) (by omega_arith) (by omega_arith) (by omega_arith)
          (by omega_arith), hi, top0] at e
      rw [Nat.add_sub_cancel, show 2 * h - (j + 1) + 1 = 2 * h - j by omega_using [hj],
        show arr w 18 + 8 * (2 * h - j) = dT + 8 * (j + 2) by omega_using [hj, hdT], e]
    · rw [fr _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), dhi]
  · rw [c28, ek.gpr .r28 (by decide)]
  · exact ((VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (js := [3]) (ds := []) (o := 3) (d := 24) eout
      (by simp only [S]; omega_arith) (by simp)).mono (js' := [18, 2, 3]) (ds' := [])).trans
      (ckw.mono (js' := [18, 2, 3]) (ds' := []))

/-- The steps: from step 1 to step `h`. -/
theorem steps_ok {t : State} {B : Addr} {Z w N h X s : Nat} (I : SqInv t B Z w N h X s 1) :
    WP isa (.loop VG.Impl.Rsa.PPC64LE.RecoverDet.sqStep (.nonzero .d .r28)) t fun t' =>
      (∃ s', SqInv t' B Z w N h X s' h) ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] t.mem t'.mem ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22, .r26,
        .r28] t t' := by
  have h2 := I.h2
  have hh := I.hh
  refine WP.mono (wp_countdown (cnt := .r28) (N := h - 1) (by omega_using [hh]) (by omega_using [h2])
    (fun i t' => (∃ s', SqInv t' B Z w N h X s' (i + 1)) ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] t.mem t'.mem ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22, .r26,
        .r28] t t')
    (fun i hi u ⟨⟨s', J⟩, ku, kr⟩ _ => WP.mono (step_ok J (by omega_using [hi])) fun u' ⟨J', c28, ku', kr'⟩ =>
      ⟨⟨J', ku.trans ku', (kr.trans kr').mono (by decide)⟩, c28⟩)
    ⟨⟨s, I⟩, VG.Proof.Rsa.KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _⟩
    (by rw [I.r28]))
    fun t' ⟨J, k1, k2⟩ => ⟨by rw [show h - 1 + 1 = h by omega_using [h2]] at J; exact J, k1, k2⟩

/-! ## The first digit -/

theorem twoH_val {w h : Nat} (hw : w = 4 * h + 6) (hh : h < 2 ^ 20) :
    (BitVec.ofNat 64 w - 6#64) >>> 1 = BitVec.ofNat 64 (2 * h) := by
  rw [show (6#64) = BitVec.ofNat 64 6 from rfl, VG.Proof.Rsa.PPC64LE.RdShift.ofNat_sub' (by omega_using [hw]) (by omega_using [hw, hh]),
    show w - 6 = 2 * (2 * h) by omega_using [hw], mont_ofNat_shr1 (by omega_using [hh])]

/-- The first digit's tail, after the loop: the remainder over `X'`'s top two words (at `r5`), `D`'s words
`h - 1`, `h` `:= 2 s₀`, and the temporary's words 0, 1 `:= 1, s₀`. -/
theorem digit0Tail_ok {u : State} {B : Addr} {Z w N h : Nat} (hW : Ws u B Z w N) (hN : 18 < N)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (h5 : u.gpr .r5 = off B (arr w 18 + 8 * (2 * h - 2))) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Tail) u fun t =>
      (t.gpr .r9 = off B (arr w 3) ∧
        t.mem = (((((u.mem.writeW (off B (arr w 18 + 8 * (2 * h - 2))) (u.gpr .r17)).writeW
          (off B (arr w 18 + 8 * (2 * h - 2) + 8)) (u.gpr .r16)).writeW (off B (arr w 2 + 8 * (h - 1)))
          (u.gpr .r18 + u.gpr .r18)).writeW (off B (arr w 2 + 8 * (h - 1) + 8)) (u.gpr .r18 >>> 63)).writeW
          (off B (arr w 3)) (BitVec.ofNat 64 1)).writeW (off B (arr w 3 + 8)) (u.gpr .r18)) ∧
      Keep [.r0, .r6, .r9, .r11] u t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  have f2 := hW.arr_fit (j := 2) (by omega_using [hN])
  have f3 := hW.arr_fit (j := 3) (by omega_using [hN])
  simp only [S] at f18 f2 f3
  refine WP.keep _ ?_ (by decide)
  have e6 : off B (arr w 2) + BitVec.ofNat 64 (2 * h) <<< 2 - 8#64 = off B (arr w 2 + 8 * (h - 1)) := by
    rw [show BitVec.ofNat 64 (2 * h) <<< 2 = BitVec.ofNat 64 (8 * h) by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]; omega_using [],
      off_add, show (8#64) = BitVec.ofNat 64 8 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega_using [h2])]
    congr 1; omega_using [h2]
  have pv : ∀ j : Nat, j < 64 → BitVec.ofNat 64 j * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w j) :=
    fun j _ => VG.Proof.Rsa.PPC64LE.Keys.ptr_val B j (S w)
  mcrun [pv 2 (by decide), pv 3 (by decide), VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Tail,
    VG.Impl.Rsa.PPC64LE.RecoverDet.twoH,
    VG.Impl.Rsa.PPC64LE.RecoverDet.wS, VG.Impl.Rsa.PPC64LE.RecoverDet.wTmp, KeyWorkspace.hdr,
    VG.Impl.Rsa.PPC64LE.Keys.ptr, h5, hW.r29, hW.r30, hW.r31,
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val, VG.Proof.Rsa.PPC64LE.Keys.hdr_eq, twoH_val hw hh, e6,
    hs.st (show arr w 18 + 8 * (2 * h - 2) + 8 ≤ Z by omega_using [hw, f18]), hs.st (show arr w 18 + 8 * (2 * h - 2) + 8 + 8 ≤ Z by omega_using [hw, f18]),
    hs.st (show arr w 2 + 8 * (h - 1) + 8 ≤ Z by omega_using [hw, f2]), hs.st (show arr w 2 + 8 * (h - 1) + 8 + 8 ≤ Z by omega_using [hw, f2]),
    hs.st (show arr w 3 + 8 ≤ Z by omega_using [f3]), hs.st (show arr w 3 + 8 + 8 ≤ Z by omega_using [hw, f3])]
  done

theorem digit0Head_ok {u : State} {B : Addr} {Z w N h : Nat} (hW : Ws u B Z w N) (hN : 18 < N)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Head) u fun t =>
      (t.gpr .r5 = off B (arr w 18 + 8 * (2 * h - 2)) ∧
        t.gpr .r14 = Mont.word u.mem B (arr w 18 + 8 * (2 * h - 2) + 8) ∧
        t.gpr .r15 = Mont.word u.mem B (arr w 18 + 8 * (2 * h - 2)) ∧
        t.gpr .r16 = BitVec.ofNat 64 0 ∧ t.gpr .r17 = BitVec.ofNat 64 0 ∧ t.gpr .r18 = BitVec.ofNat 64 0 ∧
        t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.gpr .r8 = BitVec.ofNat 64 64 ∧ t.mem = u.mem) ∧
      Keep [.r0, .r5, .r8, .r11, .r14, .r15, .r16, .r17, .r18, .r20] u t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  simp only [S] at f18
  refine WP.keep _ ?_ (by decide)
  have e5 : off B (arr w 18) + BitVec.ofNat 64 (2 * h) <<< 3 - 16#64 = off B (arr w 18 + 8 * (2 * h - 2)) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.shl3_val, off_add, show (16#64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega_using [h2])]
    congr 1; omega_using [h2]
  have pv : BitVec.ofNat 64 18 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 18) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 18 (S w)
  mcrun [pv, VG.Impl.Rsa.PPC64LE.RecoverDet.digit0Head, VG.Impl.Rsa.PPC64LE.RecoverDet.twoH,
    VG.Impl.Rsa.PPC64LE.RecoverDet.wR, KeyWorkspace.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r29, hW.r30, hW.r31,
    VG.Proof.Rsa.PPC64LE.Keys.hdr_eq, twoH_val hw hh, e5,
    hs.ld (show arr w 18 + 8 * (2 * h - 2) + 8 + 8 ≤ Z by omega_using [hw, f18]), hs.ld (show arr w 18 + 8 * (2 * h - 2) + 8 ≤ Z by omega_using [hw, f18])]
  done

theorem rdw {m : Mem} {B : Addr} {a d : Nat} (v : BitVec 64) (hsep : d + 8 ≤ a ∨ a + 8 ≤ d) (ha : a + 8 ≤ 2 ^ 64)
    (hd : d + 8 ≤ 2 ^ 64) : Mont.word (m.writeW (off B a) v) B d = Mont.word m B d :=
  (writeW_outside m B v ha).word (by omega_using [hsep]) hd

theorem wvw {m : Mem} {B : Addr} {a d k : Nat} (v : BitVec 64) (hsep : d + 8 * k ≤ a ∨ a + 8 ≤ d)
    (ha : a + 8 ≤ 2 ^ 64) (hd : d + 8 * k ≤ 2 ^ 64) : wordsVal (m.writeW (off B a) v) B d k = wordsVal m B d k :=
  (writeW_outside m B v ha).wordsVal hsep hd

theorem wv2 (m : Mem) (B : Addr) (d : Nat) :
    wordsVal m B d 2 = (Mont.word m B d).toNat + 2 ^ 64 * (Mont.word m B (d + 8)).toNat := by
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero]

theorem kwr {B : Addr} {w : Nat} {m : Mem} (o : Nat) {a : Nat} (v : BitVec 64) (ho : o ∈ [18, 2, 3])
    (h1 : arr w o ≤ a) (h2 : a + 8 ≤ arr w o + S w) (fit : a + 8 ≤ 2 ^ 64) :
    VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] m (m.writeW (off B a) v) :=
  VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (d := a - arr w o) (n := 8)
    (by rw [Nat.add_sub_cancel' h1]; exact writeW_outside m B v fit) (by omega_using [h1, h2]) ho

/-- The first digit: from `X'`'s top two words `T ≥ 2^126`, its root `s₀ ≥ 2^63` with `T - s₀²` in their
place, `D`'s top two words `2 s₀`, and the temporary's words 1 and 2 `s₀` and its reciprocal. -/
theorem digit0_ok {u : State} {B : Addr} {Z w N h : Nat} (hW : Ws u B Z w N) (hN : 18 < N)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20)
    (hT : 2 ^ 126 ≤ wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.digit0 u fun t =>
      (∃ s0, 2 ^ 63 ≤ s0 ∧ s0 < 2 ^ 64 ∧ s0 * s0 ≤ wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2 ∧
        wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2 - s0 * s0 ≤ 2 * s0 ∧
        wordsVal t.mem B (arr w 18 + 8 * (2 * h - 2)) 2 = wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2 - s0 * s0 ∧
        wordsVal t.mem B (arr w 2 + 8 * (h - 1)) 2 = 2 * s0 ∧ (Mont.word t.mem B (arr w 3 + 8)).toNat = s0 ∧
        (Mont.word t.mem B (arr w 3 + 16)).toNat = (2 ^ 128 - 1) / (Mont.word t.mem B (arr w 3 + 8)).toNat - 2 ^ 64) ∧
      wordsVal t.mem B (arr w 18) (2 * h - 2) = wordsVal u.mem B (arr w 18) (2 * h - 2) ∧
      wordsVal t.mem B (arr w 2) (h - 1) = wordsVal u.mem B (arr w 2) (h - 1) ∧
      wordsVal t.mem B (arr w 2 + 8 * (h + 1)) (h + 2) = wordsVal u.mem B (arr w 2 + 8 * (h + 1)) (h + 2) ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] u.mem t.mem ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20] u t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  have f2 := hW.arr_fit (j := 2) (by omega_using [hN])
  have f3 := hW.arr_fit (j := 3) (by omega_using [hN])
  have a23 : arr w 2 + S w ≤ arr w 3 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  have a318 : arr w 3 + S w ≤ arr w 18 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  simp only [S] at f18 f2 f3 a23 a318
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.digit0
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.mono (digit0Head_ok hW hN hw h2 hh) fun v1 ⟨⟨a5, a14, a15, a16, a17, a18, a20, a8, am⟩, ak⟩ => ?_)
  refine WP.seq (WP.mono (digit0Loop_ok a8 a16 a17 a18 a20) fun v2 ⟨l1, l2, l20, lm, lk⟩ => ?_)
  have W2 := hW.of_keep (ak.trans lk)
  refine WP.seq (WP.mono (digit0Tail_ok W2 hN hw h2 hh ((lk.gpr .r5 (by decide)).trans a5))
    fun v3 ⟨⟨t9, tm⟩, tk⟩ => ?_)
  have hs3 := hs.congr ((ak.trans lk).trans tk).wr
  have w8 : Mont.word v3.mem B (arr w 3 + 8) = v2.gpr .r18 := by rw [tm, word_writeW_self]
  have hTe : wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2 = (v1.gpr .r14).toNat * 2 ^ 64 + (v1.gpr .r15).toNat := by
    rw [wv2, a14, a15]; omega_using []
  rw [← hTe] at l1
  have hs0 : 2 ^ 63 ≤ (v2.gpr .r18).toNat := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_le_mul (show (v2.gpr .r18).toNat + 1 ≤ 2 ^ 63 by omega_using [hlt])
      (show (v2.gpr .r18).toNat + 1 ≤ 2 ^ 63 by omega_using [hlt])
    have e : ((v2.gpr .r18).toNat + 1) * ((v2.gpr .r18).toNat + 1) =
        (v2.gpr .r18).toNat * (v2.gpr .r18).toNat + 2 * (v2.gpr .r18).toNat + 1 := by ring
    rw [e] at this
    omega_using [hN, hw, h2, hh, hT, hnw, f18, f2, f3, a23, a318, a5, a14, a15, a16, a17, a18, a20, a8, l1, l2, l20, t9, w8, hTe, hlt, this, e]
  refine WP.mono (recipAt_ok hs3 t9 (by omega_using [hw, f3]) (by rw [w8]; exact hs0)) fun t ⟨⟨rv, rout⟩, rk⟩ => ?_
  have r18lt := (v2.gpr .r18).isLt
  refine ⟨⟨(v2.gpr .r18).toNat, hs0, r18lt, by omega_using [l1], by omega_using [l1, l2], ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ((((ak.trans lk).trans tk).trans rk).mono (by decide))⟩
  · rw [rout.wordsVal (by omega_using [h2, a318]) (by omega_using [hw, hnw, f18]), tm, wv2,
      rdw _ (by omega_using [h2, a318]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f18]), rdw _ (by omega_using [a318]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f18]),
      rdw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]), rdw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]),
      rdw _ (by omega_using []) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f18]), word_writeW_self,
      rdw _ (by omega_using [a318]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f18]), rdw _ (by omega_using [a318]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f18]),
      rdw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]), rdw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]), word_writeW_self]
    omega_using [l1]
  · rw [rout.wordsVal (by omega_using [hw, a23]) (by omega_using [hw, hnw, f2]), tm, wv2,
      rdw _ (by omega_using [hw, a23]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f2]), rdw _ (by omega_using [hw, a23]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f2]),
      rdw _ (by omega_using []) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f2]), word_writeW_self,
      rdw _ (by omega_using [hw, a23]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f2]), rdw _ (by omega_using [hw, a23]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f2]), word_writeW_self,
      BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega_using []
  · rw [rout.word (by omega_using []) (by omega_using [hw, hnw, f3]), w8]
  · rw [rv, rout.word (by omega_using []) (by omega_using [hw, hnw, f3])]
  · rw [rout.wordsVal (by omega_using [hw, a318]) (by omega_using [hw, hnw, f18]), tm, wvw _ (by omega_using [hw, a318]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f18]),
      wvw _ (by omega_using [a318]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f18]), wvw _ (by omega_using [hw, a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]),
      wvw _ (by omega_using [hw, a23, a318]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f18]), wvw _ (by omega_using []) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f18]),
      wvw _ (by omega_using []) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f18]), lm, am]
  · rw [rout.wordsVal (by omega_using [hw, a23]) (by omega_using [hw, hnw, f2]), tm, wvw _ (by omega_using [hw, a23]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using [hw, a23]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f2]), wvw _ (by omega_using []) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using []) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f2]), wvw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using [a23, a318]) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f2]), lm, am]
  · rw [rout.wordsVal (by omega_using [hw, a23]) (by omega_using [hw, hnw, f2]), tm, wvw _ (by omega_using [hw, a23]) (by omega_using [hw, hnw, f3]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using [hw, a23]) (by omega_using [hnw, f3]) (by omega_using [hw, hnw, f2]), wvw _ (by omega_using [h2]) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using []) (by omega_using [hw, hnw, f2]) (by omega_using [hw, hnw, f2]), wvw _ (by omega_using [hw, a23, a318]) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f2]),
      wvw _ (by omega_using [hw, a23, a318]) (by omega_using [hw, hnw, f18]) (by omega_using [hw, hnw, f2]), lm, am]
  · refine VG.Proof.Rsa.KeyWorkspace.Keep.trans ?_
      (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 3) (d := 16) rout (by simp only [S]; omega_using [hw]) (by simp))
    rw [tm, lm, am]
    refine ((((((kwr 18 _ (by simp) (by omega_using []) (by simp only [S]; omega_using [hw]) (by omega_using [hw, hnw, f18])).trans
      (kwr 18 _ (by simp) (by omega_using []) (by simp only [S]; omega_using [hw]) (by omega_using [hw, hnw, f18]))).trans
      (kwr 2 _ (by simp) (by omega_using []) (by simp only [S]; omega_using [hw]) (by omega_using [hw, hnw, f2]))).trans
      (kwr 2 _ (by simp) (by omega_using []) (by simp only [S]; omega_using [hw]) (by omega_using [hw, hnw, f2]))).trans
      (kwr 3 _ (by simp) (by omega_using []) (by simp only [S]; omega_using []) (by omega_using [hnw, f3]))).trans
      (kwr 3 _ (by simp) (by omega_using []) (by simp only [S]; omega_using [hw]) (by omega_using [hw, hnw, f3])))

theorem stepsHead_ok {u : State} {B : Addr} {Z w N h : Nat} (hW : Ws u B Z w N) (hw : w = 4 * h + 6)
    (h2 : 2 ≤ h) (hh : h < 2 ^ 20) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.stepsHead) u fun t =>
      (t.gpr .r19 = off B (arr w 18) ∧ t.gpr .r24 = off B (arr w 2) ∧ t.gpr .r26 = BitVec.ofNat 64 1 ∧
        t.gpr .r28 = BitVec.ofNat 64 (h - 1) ∧ t.mem = u.mem) ∧ Keep [.r11, .r19, .r24, .r26, .r28] u t := by
  refine WP.keep _ ?_ (by decide)
  have pv : ∀ j : Nat, j < 64 → BitVec.ofNat 64 j * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w j) :=
    fun j _ => VG.Proof.Rsa.PPC64LE.Keys.ptr_val B j (S w)
  have e28 : BitVec.ofNat 64 (2 * h) >>> 1 - 1#64 = BitVec.ofNat 64 (h - 1) := by
    rw [mont_ofNat_shr1 (by omega_using [hh]), show (1#64) = BitVec.ofNat 64 1 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.ofNat_sub' (by omega_using [h2]) (by omega_using [hh])]
  mcrun [pv 18 (by decide), pv 2 (by decide), VG.Impl.Rsa.PPC64LE.RecoverDet.stepsHead,
    VG.Impl.Rsa.PPC64LE.RecoverDet.twoH, VG.Impl.Rsa.PPC64LE.RecoverDet.wR, VG.Impl.Rsa.PPC64LE.RecoverDet.wS,
    KeyWorkspace.hdr, VG.Impl.Rsa.PPC64LE.Keys.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r29, hW.r30, hW.r31,
    twoH_val hw hh, e28]
  done

/-- The first digit and the steps' registers: the invariant at step 1, for `X` (`X'`'s `2 h` words) whose
top two words are at least `2^126`, and `D`'s low `h - 1` words zero. -/
theorem first_ok {u : State} {B : Addr} {Z w N h X : Nat} (hW : Ws u B Z w N) (hN : 18 < N)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (hX : wordsVal u.mem B (arr w 18) (2 * h) = X)
    (hT : 2 ^ 126 ≤ X / 2 ^ (64 * (2 * h - 2))) (hz : wordsVal u.mem B (arr w 2) (h - 1) = 0)
    (hzh : wordsVal u.mem B (arr w 2 + 8 * (h + 1)) (h + 2) = 0) :
    WP isa (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.digit0 (.block VG.Impl.Rsa.PPC64LE.RecoverDet.stepsHead)) u
      fun t => (∃ s, SqInv t B Z w N h X s 1) ∧ VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [] u.mem t.mem ∧
        Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r24,
          .r26, .r28] u t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  simp only [S] at f18
  have eT : X / 2 ^ (64 * (2 * h - 2)) = wordsVal u.mem B (arr w 18 + 8 * (2 * h - 2)) 2 := by
    rw [← hX, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_div (show 2 * h - 2 ≤ 2 * h by omega_using []),
      show 2 * h - (2 * h - 2) = 2 by omega_using [h2]]
  have eL : X % 2 ^ (64 * (2 * h - 2)) = wordsVal u.mem B (arr w 18) (2 * h - 2) := by
    have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append u.mem B (arr w 18) (2 * h - 2) 2
    rw [show 2 * h - 2 + 2 = 2 * h by omega_using [h2], hX] at sp
    rw [sp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]
  rw [eT] at hT
  refine WP.seq (WP.mono (digit0_ok hW hN hw h2 hh hT)
    fun v ⟨⟨s0, b1, b2, b3, b4, r1, d1, t1, t2⟩, fl, fd, fdh, fk, rk⟩ => ?_)
  refine WP.mono (stepsHead_ok (hW.of_keep rk) hw h2 hh) fun t ⟨⟨q19, q24, q26, q28, qm⟩, qk⟩ => ?_
  rw [← qm] at r1 d1 t1 t2 fl fd fdh
  refine ⟨⟨s0, ⟨hW.of_keep (rk.trans qk), hN, hw, h2, hh, le_refl _, by omega_using [h2], q19, q24, q26, by rw [q28], ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, by rw [qm]; exact fk, (rk.trans qk).mono (by decide)⟩
  · rw [show 2 * h - 2 * 1 = 2 * h - 2 by omega_using [], eT]; exact b3
  · rw [show 2 * h - 2 * 1 = 2 * h - 2 by omega_using [], eT]; exact b4
  · simpa using b1
  · simpa using b2
  · rw [show 2 * h - 2 * 1 = 2 * h - 2 by omega_using [], fl, eL]
  · rw [show 2 * h - 2 * 1 = 2 * h - 2 by omega_using [], r1, eT]
  · rw [show h - 1 = h - 1 by rfl]; exact d1
  · rw [fd, hz]
  · simpa using t1
  · exact t2
  · rfl
  · rw [fdh, hzh]

end Step

/-! ## The leading zeros' stages -/

section Clz
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE

theorem shr_zero_iff (z : BitVec 64) (b : Nat) : z >>> (64 - b) = 0#64 ↔ z.toNat < 2 ^ (64 - b) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl

/-- A stage of a word's leading zeros, `b = 2^lg`: `r11 := r11 << b` and `r12 := r12 + b` if `r11 < 2^(64 - b)`. -/
theorem clzStage_ok {s : State} {lg : Nat} (hlg : lg < 6) (z acc : BitVec 64) (h11 : s.gpr .r11 = z)
    (h12 : s.gpr .r12 = acc) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.clzStage (2 ^ lg) lg)) s fun u =>
      (u.gpr .r11 = (if z.toNat < 2 ^ (64 - 2 ^ lg) then z <<< 2 ^ lg else z) ∧
        u.gpr .r12 = acc + BitVec.ofNat 64 (if z.toNat < 2 ^ (64 - 2 ^ lg) then 2 ^ lg else 0) ∧ u.mem = s.mem) ∧
      Keep [.r0, .r3, .r6, .r11, .r12] s u := by
  have h1 : 1 ≤ 2 ^ lg := Nat.one_le_two_pow
  have h64 : 2 ^ lg < 64 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hlg) (by decide)
  refine WP.keep _ ?_ (by rfl)
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.clzStage, h11, h12, exec_lsr_d (show 64 - 2 ^ lg < 64 by omega_using [h1]),
    exec_lsl (show lg < 64 by omega_using [hlg]), exec_lsl (show 2 ^ lg < 64 by omega_using [h64])]
  have e1 : (z >>> (64 - 2 ^ lg) ||| 0#64 - z >>> (64 - 2 ^ lg)) >>> 63 ^^^ 1#64 =
      BitVec.ofNat 64 (if z.toNat < 2 ^ (64 - 2 ^ lg) then 1 else 0) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.nz_bit]
    by_cases hc : z.toNat < 2 ^ (64 - 2 ^ lg)
    · have hz := (shr_zero_iff z (2 ^ lg)).mpr hc
      simp only [hz, hc, ↓reduceIte]; rfl
    · have hz : ¬ z >>> (64 - 2 ^ lg) = 0#64 := fun h => hc ((shr_zero_iff z _).mp h)
      simp only [hz, hc, ↓reduceIte]; rfl
  rw [e1]
  by_cases hc : z.toNat < 2 ^ (64 - 2 ^ lg)
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [show (0#64 - BitVec.ofNat 64 1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
        BitVec.xor_comm (z <<< 2 ^ lg) z, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mul]
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [show (0#64 - BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]
    · congr 1
      apply BitVec.eq_of_toNat_eq
      simp

/-- The stages' sizes, `2^k` down to `1`. -/
def lgsDown : Nat → List Nat
  | 0 => [0]
  | k + 1 => (k + 1) :: lgsDown k

/-- The stages `2^k … 1` on `z₀ 2^a` (`r11`, `a` in `r12`) at least `2^(64 - 2^(k+1))`: the word shifted up
until its top bit is set, `z₀ 2^a' ∈ [2^63, 2^64)`. -/
theorem clzStages_ok {z0 : Nat} : ∀ (k : Nat) (s : State) (a : Nat), k < 6 → z0 * 2 ^ a < 2 ^ 64 →
    2 ^ (64 - 2 ^ (k + 1)) ≤ z0 * 2 ^ a → s.gpr .r11 = BitVec.ofNat 64 (z0 * 2 ^ a) →
    s.gpr .r12 = BitVec.ofNat 64 a →
    WP isa (.block ((lgsDown k).flatMap fun lg => VG.Impl.Rsa.PPC64LE.RecoverDet.clzStage (2 ^ lg) lg)) s fun u =>
      (∃ a', 2 ^ 63 ≤ z0 * 2 ^ a' ∧ z0 * 2 ^ a' < 2 ^ 64 ∧ a ≤ a' ∧ a' ≤ a + 2 ^ (k + 1) ∧
        u.gpr .r11 = BitVec.ofNat 64 (z0 * 2 ^ a') ∧ u.gpr .r12 = BitVec.ofNat 64 a') ∧ u.mem = s.mem ∧
      Keep [.r0, .r3, .r6, .r11, .r12] s u
  | k, s, a, hk, hlt, hge, h11, h12 => by
    have hst := clzStage_ok (lg := k) hk _ _ h11 h12
    have hb : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hk64 : 2 ^ (k + 1) ≤ 64 := Nat.pow_le_pow_right (by decide) (show k + 1 ≤ 6 by omega_using [hk])
    have hc : (BitVec.ofNat 64 (z0 * 2 ^ a)).toNat = z0 * 2 ^ a := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hc] at hst
    -- After this stage: `z₀ 2^b` with `b = a + 2^k` if it fits, at least `2^(64 - 2^k)`.
    obtain ⟨b, hb1, hb2, hb3, hb4, e11, e12⟩ : ∃ b, a ≤ b ∧ b ≤ a + 2 ^ k ∧ z0 * 2 ^ b < 2 ^ 64 ∧
        2 ^ (64 - 2 ^ k) ≤ z0 * 2 ^ b ∧
        (if z0 * 2 ^ a < 2 ^ (64 - 2 ^ k) then BitVec.ofNat 64 (z0 * 2 ^ a) <<< 2 ^ k
          else BitVec.ofNat 64 (z0 * 2 ^ a)) = BitVec.ofNat 64 (z0 * 2 ^ b) ∧
        BitVec.ofNat 64 a + BitVec.ofNat 64 (if z0 * 2 ^ a < 2 ^ (64 - 2 ^ k) then 2 ^ k else 0) =
          BitVec.ofNat 64 b := by
      by_cases hcc : z0 * 2 ^ a < 2 ^ (64 - 2 ^ k)
      · have ep : z0 * 2 ^ (a + 2 ^ k) = z0 * 2 ^ a * 2 ^ 2 ^ k := by rw [Nat.pow_add, Nat.mul_assoc]
        have up : z0 * 2 ^ a * 2 ^ 2 ^ k < 2 ^ 64 := by
          have := Nat.mul_lt_mul_of_pos_right hcc (Nat.two_pow_pos (2 ^ k))
          rwa [← Nat.pow_add, show 64 - 2 ^ k + 2 ^ k = 64 by omega] at this
        refine ⟨a + 2 ^ k, by omega, le_refl _, by rw [ep]; exact up, ?_, ?_, ?_⟩
        · rw [ep]
          have := Nat.mul_le_mul_right (2 ^ 2 ^ k) hge
          rwa [← Nat.pow_add, show 64 - 2 ^ (k + 1) + 2 ^ k = 64 - 2 ^ k by omega_using [hk64]] at this
        · simp only [hcc, ↓reduceIte]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hc, BitVec.toNat_ofNat, ep, Nat.mod_eq_of_lt up]
        · simp only [hcc, ↓reduceIte, BitVec.ofNat_add]
      · refine ⟨a, le_refl _, by omega, hlt, by omega_using [hcc], by simp only [hcc, ↓reduceIte], ?_⟩
        simp only [hcc, ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp
    cases k with
    | zero =>
      simp only [lgsDown, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine WP.mono hst fun u ⟨⟨u11, u12, um⟩, uk⟩ => ⟨⟨b, by simpa using hb4, hb3, hb1,
        by simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one] at hb2 ⊢; omega_using [hb2],
        by rw [u11, e11], by rw [u12, e12]⟩, um, uk⟩
    | succ k =>
      simp only [lgsDown, List.flatMap_cons]
      refine WP.block_append (WP.mono hst fun u ⟨⟨u11, u12, um⟩, uk⟩ => ?_)
      rw [e11] at u11
      rw [e12] at u12
      refine WP.mono (clzStages_ok k u b (by omega_using [hk]) hb3 (by simpa using hb4) u11 u12)
        fun t ⟨⟨a', t1, t2, t3, t4, t5, t6⟩, tm, tk⟩ =>
          ⟨⟨a', t1, t2, by omega_using [hb1, t3], by rw [Nat.pow_succ] at hb2 ⊢; omega_using [hb2, t4], t5, t6⟩, by rw [tm, um],
            (uk.trans tk).mono (by decide)⟩

end Clz

/-! ## The scan for the top word -/

section ClzX
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.RdShift (ClzOf clz_step zmask off_sub)
open VG.Impl.Rsa.PPC64LE.Keys (countLoop)

/-- `clzX`'s scan body. -/
abbrev clzXBody : List Instr :=
  [.load .d .r0 .r5 0, .logic .and .r3 .r0 .r9, .logic .or .r11 .r11 .r3, .li .r3 0,
    .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63, .subi .r3 .r3 1, .logic .and .r9 .r9 .r3,
    .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3, .subi .r5 .r5 8]

/-- The top word that is not zero of `T` (`i` words, `r` leading zero words). -/
def topW (T i r : Nat) : Nat := if T = 0 then 0 else T / 2 ^ (64 * (i - r - 1))

theorem topW_step {T y i r : Nat} (h : ClzOf T i r) (hy : y < 2 ^ 64) :
    topW (y + 2 ^ 64 * T) (i + 1) (if T = 0 ∧ y = 0 then i + 1 else r) = if T = 0 then y else topW T i r := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hT : T = 0
  · have hr := h2 hT
    subst hT hr
    by_cases hy0 : y = 0
    · subst hy0; simp [topW]
    · simp [topW, hy0]
  · obtain ⟨lo, hi⟩ := h3 hT
    have hir : 1 ≤ i - r := by
      refine Nat.pos_of_ne_zero fun e => ?_
      rw [e, Nat.mul_zero, Nat.pow_zero] at hi
      omega_using [hT, hi]
    have hne : y + 2 ^ 64 * T ≠ 0 := by have := Nat.mul_pos (Nat.two_pow_pos 64) (Nat.pos_of_ne_zero hT); omega_using [hT]
    simp only [topW, hT, hne, false_and, ↓reduceIte]
    rw [show 64 * (i + 1 - r - 1) = 64 + 64 * (i - r - 1) by omega_using [hir], Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hy, Nat.zero_add]

theorem clzXScan_ok {s : State} {B : Addr} {Z d H : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B (d + 8 * H - 8)) (h8 : s.gpr .r8 = BitVec.ofNat 64 H)
    (h9 : s.gpr .r9 = BitVec.allOnes 64) (h10 : s.gpr .r10 = BitVec.ofNat 64 0) (h11 : s.gpr .r11 = BitVec.ofNat 64 0)
    (hH : 1 ≤ H) (hH' : H < 2 ^ 32) (hd8 : 8 ≤ d) (hd : d + 8 * H ≤ Z) :
    WP isa (countLoop .r8 clzXBody) s fun t =>
      (∃ r, t.gpr .r10 = BitVec.ofNat 64 r ∧ ClzOf (wordsVal s.mem B d H) H r ∧
        (t.gpr .r11).toNat = topW (wordsVal s.mem B d H) H r) ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r8, .r9, .r10, .r11] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (d + 8 * (H - i) - 8) ∧ t.mem = s.mem ∧
      t.gpr .r9 = (if wordsVal s.mem B (d + 8 * (H - i)) i = 0 then BitVec.allOnes 64 else 0#64) ∧
      (∃ r, t.gpr .r10 = BitVec.ofNat 64 r ∧ ClzOf (wordsVal s.mem B (d + 8 * (H - i)) i) i r ∧
        (t.gpr .r11).toNat = topW (wordsVal s.mem B (d + 8 * (H - i)) i) i r) ∧
      Keep [.r0, .r3, .r5, .r8, .r9, .r10, .r11] s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := H) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jm, j9, ⟨r, j10, jc, j11⟩, jk⟩ hc => ?_)
    ⟨by rw [h5, Nat.sub_zero], rfl, by rw [h9]; rfl, ⟨0, h10, by simp [ClzOf, wordsVal],
      by rw [h11]; simp [topW, wordsVal]⟩, Keep.refl _ _⟩ h8)
    fun t ⟨_, jm, _, jr, jk⟩ => ⟨by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jr; exact jr, jm, jk⟩
  have ek : d + 8 * (H - i) - 8 = d + 8 * (H - 1 - i) := by omega_arith
  rw [ek] at j5
  have hst : WP isa (.block (clzXBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (d + 8 * (H - 1 - i)) - BitVec.ofNat 64 8 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem ∧
        t'.gpr .r11 = t.gpr .r11 ||| (word t.mem B (d + 8 * (H - 1 - i)) &&& t.gpr .r9) ∧
        t'.gpr .r9 = t.gpr .r9 &&& ((BitVec.ofNat 64 0 - word t.mem B (d + 8 * (H - 1 - i)) |||
          word t.mem B (d + 8 * (H - 1 - i))) >>> 63 - BitVec.ofNat 64 1) ∧
        t'.gpr .r10 = t.gpr .r10 + (t'.gpr .r9 &&& BitVec.ofNat 64 1)) ∧
      Keep [.r0, .r3, .r5, .r8, .r9, .r10, .r11] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, (hs.congr jk.wr).ld (show d + 8 * (H - 1 - i) + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm, l11, l9, l10⟩, lk⟩ => ?_
  rw [jm, zmask] at l9
  rw [jm] at l11
  generalize hy : word s.mem B (d + 8 * (H - 1 - i)) = y at l9 l10 l11
  have hsucc : wordsVal s.mem B (d + 8 * (H - (i + 1))) (i + 1) =
      y.toNat + 2 ^ 64 * wordsVal s.mem B (d + 8 * (H - i)) i := by
    rw [show d + 8 * (H - (i + 1)) = d + 8 * (H - 1 - i) by omega_arith,
      VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, hy,
      show d + 8 * (H - 1 - i) + 8 = d + 8 * (H - i) by omega_arith]
  have hy0 : y = 0#64 ↔ y.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  have cs := clz_step jc y.isLt
  have ts := topW_step jc y.isLt
  rw [← hsucc] at cs ts
  generalize wordsVal s.mem B (d + 8 * (H - i)) i = T at j9 jc cs hsucc j11 ts
  refine ⟨⟨?_, by rw [lm, jm], ?_, ⟨_, ?_, cs, ?_⟩, jk.trans' lk⟩, l8⟩
  · rw [l5, off_sub B (by omega_arith)]; congr 1; omega_arith
  · rw [l9, j9, hsucc]
    by_cases hT : T = 0
    · subst hT
      by_cases hyz : y = 0#64
      · subst hyz; simp
      · simp [hyz, hy0.not.mp hyz]
    · have hne : y.toNat + 2 ^ 64 * T ≠ 0 := fun e => hT (by omega_using [e])
      simp only [hT, hne, ↓reduceIte, BitVec.zero_and]
  · rw [l10, l9, j9, j10]
    by_cases hT : T = 0
    · have hr := jc.2.1 hT
      subst hT hr
      by_cases hyz : y = 0#64
      · subst hyz
        simp only [↓reduceIte, BitVec.and_allOnes]
        (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) <;> omega_arith
      · simp [hyz, hy0.not.mp hyz]
    · simp [hT]
  · rw [ts, l11, j9]
    by_cases hT : T = 0
    · have hr := jc.2.1 hT
      subst hT hr
      have : ∀ a b, topW 0 a b = 0 := fun _ _ => by simp [topW]
      rw [this] at j11
      have e0 : t.gpr .r11 = 0#64 := BitVec.eq_of_toNat_eq j11
      simp only [↓reduceIte, e0, BitVec.zero_or, BitVec.and_allOnes]
    · simp only [hT, ↓reduceIte, BitVec.and_zero, BitVec.or_zero]
      exact j11

end ClzX

/-! ## The counts -/

section Counts
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S slot)
open VG.Impl.Rsa.PPC64LE.RecoverDet (sQw sQb sRw sRb)

theorem counts_eq : VG.Impl.Rsa.PPC64LE.RecoverDet.counts = ([.li .r12 0] : List Instr) ++
    ((lgsDown 5).flatMap fun lg => VG.Impl.Rsa.PPC64LE.RecoverDet.clzStage (2 ^ lg) lg) ++
    ([.store .w .r10 .r31 sQw, .lsr .d .r0 .r12 1, .lsl .r3 .r0 1, .store .w .r3 .r31 sQb,
      .lsl .r4 .r10 6, .add .r4 .r4 .r12, .lsr .d .r4 .r4 1, .addi .r4 .r4 1, .lsr .d .r3 .r4 6,
      .store .w .r3 .r31 sRw, .li .r3 63, .logic .and .r3 .r4 .r3, .store .w .r3 .r31 sRb] : List Instr) := rfl

/-- The counts: from the leading zero words `c_w` (`r10`) and the top word `z₀ ≠ 0` (`r11`), its leading
zero bits `c_b` (`z₀ 2^c_b ∈ [2^63, 2^64)`), and the slots `sQw = c_w`, `sQb = c_b - c_b mod 2`,
`sRw`, `sRb` the words and bits of `⌊(64 c_w + c_b) / 2⌋ + 1`. -/
theorem counts_ok {s : State} {B : Addr} {Z w N cw z0 : Nat} (hW : Ws s B Z w N) (h10 : s.gpr .r10 = BitVec.ofNat 64 cw)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 z0) (hcw : cw < 2 ^ 21) (hz0 : 0 < z0) (hz : z0 < 2 ^ 64) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.counts) s fun t =>
      (∃ cb, 2 ^ 63 ≤ z0 * 2 ^ cb ∧ z0 * 2 ^ cb < 2 ^ 64 ∧ cb < 64 ∧
        slot t.mem B sQw = cw ∧ slot t.mem B sQb = cb / 2 * 2 ∧
        slot t.mem B sRw = ((64 * cw + cb) / 2 + 1) / 64 ∧ slot t.mem B sRb = ((64 * cw + cb) / 2 + 1) % 64) ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [] [sQw, sQb, sRw, sRb] s.mem t.mem ∧
      slot t.mem B 92 = slot s.mem B 92 ∧ Keep [.r0, .r3, .r4, .r6, .r11, .r12] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have hz160 : 160 ≤ Z := hW.hdr_le
  rw [counts_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) (by prun)
    (by decide)) fun u ⟨⟨u12, um⟩, uk⟩ => ?_
  refine WP.mono (clzStages_ok (z0 := z0) 5 u 0 (by decide) (by simpa using hz) (by simpa using Nat.succ_le_of_lt hz0)
    (by rw [uk.gpr .r11 (by decide), h11]; simp) (by rw [u12]))
    fun v ⟨⟨cb, c1, c2, _, c4, v11, v12⟩, vm, vk⟩ => ?_
  have hcb : cb < 64 := by
    refine Nat.lt_of_not_le fun h => ?_
    have := Nat.mul_le_mul (show 1 ≤ z0 by omega_using [hz0]) (Nat.pow_le_pow_right (show 0 < 2 by decide) h)
    omega_arith
  have hs2 := hs.congr (uk.trans vk).wr
  have e10 : v.gpr .r10 = BitVec.ofNat 64 cw := by rw [(uk.trans vk).gpr .r10 (by decide), h10]
  have e31 : v.gpr .r31 = B := by rw [(uk.trans vk).gpr .r31 (by decide), hW.r31]
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun t => t.mem = (((v.mem.writeW (off B sQw)
      ((BitVec.ofNat 64 cw).setWidth 32)).writeW (off B sQb) ((BitVec.ofNat 64 cb >>> 1 <<< 1).setWidth 32)).writeW
      (off B sRw) (BitVec.setWidth 32 (((BitVec.ofNat 64 cw <<< 6 + BitVec.ofNat 64 cb) >>> 1 + 1#64) >>> 6))).writeW
      (off B sRb) (BitVec.setWidth 32 (((BitVec.ofNat 64 cw <<< 6 + BitVec.ofNat 64 cb) >>> 1 + 1#64) &&&
        BitVec.ofNat 64 63))) (by
    prun [e10, v12, e31, sQw, sQb, sRw, sRb, hs2.st (show 76 + 4 ≤ Z by omega_using [hz160]), hs2.st (show 80 + 4 ≤ Z by omega_using [hz160]),
      hs2.st (show 84 + 4 ≤ Z by omega_using [hz160]), hs2.st (show 88 + 4 ≤ Z by omega_using [hz160]),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 76 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 80 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 84 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 88 < 2 ^ 15 by decide)]
    done) (by decide)) fun t ⟨tm, tk⟩ => ?_
  rw [vm, um] at tm
  simp only [sQw, sQb, sRw, sRb] at tm ⊢
  have sw := fun (m : Mem) (d e : Nat) (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 100) (he : e < 100) =>
    VG.Proof.Rsa.PPC64LE.Recover.slot_wne m B v h (by omega_using [hd]) (by omega_using [he])
  have ss := VG.Proof.Rsa.PPC64LE.Keys.slot_write_self
  refine ⟨⟨cb, c1, c2, hcb, ?_, ?_, ?_, ?_⟩, ?_, ?_, ((uk.trans vk).trans tk).mono (by decide)⟩
  · rw [tm, sw _ 88 76 _ (by decide) (by decide) (by decide), sw _ 84 76 _ (by decide) (by decide) (by decide), sw _ 80 76 _ (by decide) (by decide) (by decide), ss]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hcw]
  · rw [tm, sw _ 88 80 _ (by decide) (by decide) (by decide), sw _ 84 80 _ (by decide) (by decide) (by decide), ss]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega_using [c4]
  · rw [tm, sw _ 88 84 _ (by decide) (by decide) (by decide), ss]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_add, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega_using [hcw, c4]
  · rw [tm, ss]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_add, BitVec.toNat_and, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl] at *
    rw [show (2 ^ 6 - 1) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega_using []
  · rw [tm]
    exact (((VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by omega_using [])).trans
      (VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by omega_using []))).trans
      (VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by omega_using []))).trans
      (VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by omega_using []))
  · rw [tm, sw _ 88 92 _ (by decide) (by decide) (by decide), sw _ 84 92 _ (by decide) (by decide) (by decide),
      sw _ 80 92 _ (by decide) (by decide) (by decide), sw _ 76 92 _ (by decide) (by decide) (by decide)]

end Counts

/-! ## Normalization -/

/-- `X ≠ 0` (`n` words, `cw` leading zero words, its top word `z₀`, `z₀ 2^cb ∈ [2^63, 2^64)`) shifted up by
`64 cw + 2 ⌊cb / 2⌋` still has `n` words, its top two at least `2^126`. -/
theorem norm_bounds {X n cw cb : Nat} (hn : 2 ≤ n) (hX : X ≠ 0) (hc : VG.Proof.Rsa.PPC64LE.RdShift.ClzOf X n cw)
    (h1 : 2 ^ 63 ≤ topW X n cw * 2 ^ cb) (h2 : topW X n cw * 2 ^ cb < 2 ^ 64) :
    X * 2 ^ (64 * cw + cb / 2 * 2) < 2 ^ (64 * n) ∧
    2 ^ 126 ≤ X * 2 ^ (64 * cw + cb / 2 * 2) / 2 ^ (64 * (n - 2)) := by
  obtain ⟨c1, -, c3⟩ := hc
  obtain ⟨lo, hi⟩ := c3 hX
  have hcw : cw + 1 ≤ n := by
    refine Nat.lt_of_not_le fun h => ?_
    rw [show n - cw = 0 by omega_using [h], Nat.mul_zero, Nat.pow_zero] at hi
    omega_using [hX, hi]
  simp only [topW, hX, ↓reduceIte] at h1 h2
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (64 * (n - cw - 1)) := ⟨_, rfl⟩
  rw [← hP] at h1 h2 lo
  have hPp : 0 < P := by rw [hP]; exact Nat.two_pow_pos _
  have eT : 2 ^ (64 * (n - cw)) = P * 2 ^ 64 := by rw [hP, ← Nat.pow_add]; congr 1; omega_using [hcw]
  rw [eT] at hi
  have eN : 2 ^ (64 * n) = P * 2 ^ (64 * cw) * 2 ^ 64 := by
    rw [hP, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hcw]
  have eN2 : 2 ^ (64 * (n - 2)) * 2 ^ 64 = P * 2 ^ (64 * cw) := by
    rw [hP, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hn, hcw]
  have hq := Nat.div_add_mod X P
  have hr := Nat.mod_lt X hPp
  generalize X / P = z at h1 h2 hq
  generalize X % P = rr at hq hr
  have ec : 2 ^ (64 * cw + cb / 2 * 2) = 2 ^ (64 * cw) * 2 ^ (cb / 2 * 2) := Nat.pow_add _ _ _
  rw [ec]
  have hcb : cb / 2 * 2 ≤ cb := Nat.div_mul_le_self _ _
  have pcb : 2 ^ (cb / 2 * 2) * 2 ^ (cb - cb / 2 * 2) = 2 ^ cb := by rw [← Nat.pow_add]; congr 1; omega_using []
  have hd : cb - cb / 2 * 2 ≤ 1 := by omega_using []
  obtain ⟨G, hG⟩ : ∃ G, G = 2 ^ (cb / 2 * 2) := ⟨_, rfl⟩
  rw [← hG] at pcb ⊢
  have hGp : 0 < G := by rw [hG]; exact Nat.two_pow_pos _
  -- `(z + 1) G ≤ 2^64` and `z G ≥ 2^62`.
  have u1 : (z + 1) * G ≤ 2 ^ 64 := by
    have hz1 : 1 ≤ z := Nat.pos_of_ne_zero fun e => by rw [e] at h1; omega_using [hn, hX, c1, c3, hcw, hi, lo, hP, hPp, eT, eN, eN2, h1, h2, hq, hr, ec, hcb, hd, pcb, hG, hGp, e]
    have hcb64 : cb < 64 := by
      refine Nat.lt_of_not_le fun hb => ?_
      have := Nat.mul_le_mul hz1 (Nat.pow_le_pow_right (show 0 < 2 by decide) hb)
      omega_using [hn, hX, c1, c3, hcw, hi, lo, hP, hPp, eT, eN, eN2, h1, h2, hq, hr, ec, hcb, hd, pcb, hG, hGp, hz1, hb, this]
    have e64 : 2 ^ (64 - cb) * 2 ^ cb = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_using [hcb64]
    have hz : z < 2 ^ (64 - cb) := by
      rw [← e64] at h2; exact Nat.lt_of_mul_lt_mul_right h2
    have hGc : G ≤ 2 ^ cb := by rw [hG]; exact Nat.pow_le_pow_right (by decide) hcb
    calc (z + 1) * G ≤ 2 ^ (64 - cb) * 2 ^ cb := Nat.mul_le_mul hz hGc
      _ = 2 ^ 64 := e64
  have u2 : 2 ^ 62 ≤ z * G := by
    rw [← pcb] at h1
    have : 2 ^ (cb - cb / 2 * 2) ≤ 2 := by
      rcases (show cb - cb / 2 * 2 = 0 ∨ cb - cb / 2 * 2 = 1 by omega_using []) with e | e <;> rw [e] <;> decide
    have := Nat.mul_le_mul_left (z * G) this
    have e : z * (G * 2 ^ (cb - cb / 2 * 2)) = z * G * 2 ^ (cb - cb / 2 * 2) := by ring
    omega_using [h1, this, e]
  constructor
  · rw [eN, ← hq]
    calc (P * z + rr) * (2 ^ (64 * cw) * G) < (P * z + P) * (2 ^ (64 * cw) * G) :=
          Nat.mul_lt_mul_of_pos_right (by omega_using [hr]) (Nat.mul_pos (Nat.two_pow_pos _) hGp)
      _ = P * 2 ^ (64 * cw) * ((z + 1) * G) := by ring
      _ ≤ P * 2 ^ (64 * cw) * 2 ^ 64 := Nat.mul_le_mul_left _ u1
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← hq]
    have : 2 ^ 126 * 2 ^ (64 * (n - 2)) = 2 ^ 62 * (2 ^ (64 * (n - 2)) * 2 ^ 64) := by
      rw [show (2 : Nat) ^ 126 = 2 ^ 62 * 2 ^ 64 by norm_num]; ring
    rw [this, eN2]
    calc 2 ^ 62 * (P * 2 ^ (64 * cw)) ≤ z * G * (P * 2 ^ (64 * cw)) := Nat.mul_le_mul_right _ u2
      _ = P * z * (2 ^ (64 * cw) * G) := by ring
      _ ≤ (P * z + rr) * (2 ^ (64 * cw) * G) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)


/-! ## Whether `X` is zero -/

section ZeroX
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S slot)
open VG.Impl.Rsa.PPC64LE.Keys (countLoop)

theorem or_zero_iff (a b : BitVec 64) : a ||| b = 0#64 ↔ a = 0#64 ∧ b = 0#64 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, BitVec.toNat_zero, Nat.or_eq_zero_iff] at this
    exact ⟨BitVec.eq_of_toNat_eq this.1, BitVec.eq_of_toNat_eq this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The OR of `n` words from `d` (`r5`) into `r9`: zero exactly where they are. -/
theorem orLoop_ok {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B d)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : s.gpr .r9 = BitVec.ofNat 64 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hd : d + 8 * n ≤ Z) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .logic .or .r9 .r9 .r0, .addi .r5 .r5 8]) s fun t =>
      (t.gpr .r9 = 0#64 ↔ wordsVal s.mem B d n = 0) ∧ t.mem = s.mem ∧ Keep [.r0, .r5, .r8, .r9] s t := by
  have hnw := hs.nowrap
  refine WP.mono (wp_countdown (cnt := .r8) (N := n) (by omega_using [hn']) (by omega_using [hn])
    (fun i t => t.gpr .r5 = off B (d + 8 * i) ∧ (t.gpr .r9 = 0#64 ↔ wordsVal s.mem B d i = 0) ∧ t.mem = s.mem ∧
      Keep [.r0, .r5, .r8, .r9] s t)
    (fun i hi t ⟨j5, j9, jm, jk⟩ _ => ?_) ⟨by rw [h5]; rfl, by rw [h9]; simp [wordsVal], rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, j9, jm, jk⟩ => ⟨j9, jm, jk⟩
  refine WP.mono (WP.keep [.r0, .r5, .r8, .r9] (Q := fun t' => t'.gpr .r5 = off B (d + 8 * i + 8) ∧
      t'.gpr .r9 = t.gpr .r9 ||| Mont.word s.mem B (d + 8 * i) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
      t'.mem = t.mem) (by
    mcrun [j5, jm, (hs.congr jk.wr).ld (show d + 8 * i + 8 ≤ Z by omega_using [hd, hi])]) (by decide)) fun t' ⟨⟨u5, u9, u8, um⟩, uk⟩ => ⟨⟨by rw [u5]; congr 1, ?_, by rw [um, jm], jk.trans' uk⟩, u8⟩
  rw [u9, or_zero_iff, j9, wordsVal_succ_top]
  have hw0 : Mont.word s.mem B (d + 8 * i) = 0#64 ↔ (Mont.word s.mem B (d + 8 * i)).toNat = 0 :=
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [hw0]
  have := Nat.two_pow_pos (64 * i)
  constructor
  · rintro ⟨a, b⟩; rw [a, b]; simp
  · intro h
    have h1 : wordsVal s.mem B d i = 0 := by
      have := Nat.le_add_right (wordsVal s.mem B d i) (2 ^ (64 * i) * (Mont.word s.mem B (d + 8 * i)).toNat); omega_using [h]
    rw [h1, Nat.zero_add] at h
    exact ⟨h1, (Nat.mul_eq_zero.mp h).resolve_left (by omega_using [this])⟩

/-- `zeroX`: whether `X` (`X'`'s `2 h` words) is zero into `sZ`, and `X := 1` if so. -/
theorem zeroX_ok {s : State} {B : Addr} {Z w N h X : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hw : w = 4 * h + 6)
    (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (hX : wordsVal s.mem B (arr w 18) (2 * h) = X) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.zeroX s fun t =>
      wordsVal t.mem B (arr w 18) (2 * h) = (if X = 0 then 1 else X) ∧
      slot t.mem B VG.Impl.Rsa.PPC64LE.RecoverDet.sZ = (if X = 0 then 1 else 0) ∧
      Outside B (arr w 18) 8 (s.mem.writeW (off B VG.Impl.Rsa.PPC64LE.RecoverDet.sZ)
        (BitVec.ofNat 32 (if X = 0 then 1 else 0))) t.mem ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18] [VG.Impl.Rsa.PPC64LE.RecoverDet.sZ] s.mem t.mem ∧
      Ws t B Z w N ∧ Keep [.r0, .r3, .r5, .r8, .r9, .r11] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  simp only [S] at f18
  have hz160 : 160 ≤ Z := hW.hdr_le
  have pv : BitVec.ofNat 64 18 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 18) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 18 (S w)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.zeroX
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.mono (WP.keep [.r5, .r8, .r9, .r11] (Q := fun u => u.gpr .r5 = off B (arr w 18) ∧
      u.gpr .r8 = BitVec.ofNat 64 (2 * h) ∧ u.gpr .r9 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) (by
    mcrun [pv, VG.Impl.Rsa.PPC64LE.RecoverDet.twoH, VG.Impl.Rsa.PPC64LE.RecoverDet.wR, KeyWorkspace.hdr,
      VG.Impl.Rsa.PPC64LE.Keys.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r29, hW.r30, hW.r31, twoH_val hw hh,
      BitVec.add_zero]) (by decide)) fun u ⟨⟨u5, u8, u9, um⟩, uk⟩ => ?_)
  refine WP.seq (WP.mono (orLoop_ok (hs.congr uk.wr) u5 u8 u9 (by omega_using [h2]) (by omega_using [hh]) (by omega_using [hw, f18]))
    fun v ⟨v9, vm, vk⟩ => ?_)
  rw [um, hX] at v9
  have hW2 := hW.of_keep (uk.trans vk)
  have hs2 := hW2.scr
  obtain ⟨z, hz⟩ : ∃ z : Nat, z = if X = 0 then 1 else 0 := ⟨_, rfl⟩
  have e3 : (0#64 - v.gpr .r9 ||| v.gpr .r9) >>> 63 ^^^ 1#64 = BitVec.ofNat 64 z := by
    rw [BitVec.or_comm, VG.Proof.Rsa.PPC64LE.RdShift.nz_bit, hz]
    by_cases h0 : v.gpr .r9 = 0#64
    · simp only [h0, ↓reduceIte, v9.mp h0]; rfl
    · have : X ≠ 0 := fun e => h0 (v9.mpr e)
      simp only [h0, this, ↓reduceIte]; rfl
  have h18 : 160 ≤ arr w 18 := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr _
  have r0 : (v.mem.writeW (off B VG.Impl.Rsa.PPC64LE.RecoverDet.sZ) ((BitVec.ofNat 64 z).setWidth 32)).readW
      (off B (arr w 18)) 64 = Mont.word v.mem B (arr w 18) :=
    (writeW32_outside v.mem B (d := 92) _ (by omega_using [])).word (by omega_using [h18]) (by omega_using [hnw, f18])
  have pv : BitVec.ofNat 64 18 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 18) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 18 (S w)
  refine WP.mono (WP.keep [.r0, .r3, .r5] (Q := fun t => t.mem = (v.mem.writeW
      (off B VG.Impl.Rsa.PPC64LE.RecoverDet.sZ) ((BitVec.ofNat 64 z).setWidth 32)).writeW (off B (arr w 18))
      (Mont.word v.mem B (arr w 18) ||| BitVec.ofNat 64 z)) (by
    mcrun [pv, e3, r0, VG.Impl.Rsa.PPC64LE.RecoverDet.wR, KeyWorkspace.hdr, VG.Impl.Rsa.PPC64LE.Keys.hdr,
      VG.Impl.Rsa.PPC64LE.Keys.ptr, hW2.r30, hW2.r31, VG.Impl.Rsa.PPC64LE.RecoverDet.sZ,
      hs2.st (show 92 + 4 ≤ Z by omega_using [hz160]), hs2.ld (show arr w 18 + 8 ≤ Z by omega_using [f18]),
      hs2.st (show arr w 18 + 8 ≤ Z by omega_using [f18]),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 92 < 2 ^ 15 by decide)]
    simp only [VG.Impl.Rsa.PPC64LE.RecoverDet.sZ] at r0
    rw [show B + 92#64 = off B 92 from rfl, r0]) (by decide)) fun t ⟨tm, tk⟩ => ?_
  rw [vm, um] at tm r0
  have ez : (BitVec.ofNat 64 z).setWidth 32 = BitVec.ofNat 32 (if X = 0 then 1 else 0) := by
    rw [← hz]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [hz]; split <;> rfl
  rw [ez] at tm r0
  simp only [VG.Impl.Rsa.PPC64LE.RecoverDet.sZ] at tm r0 ⊢
  have hup : wordsVal t.mem B (arr w 18 + 8) (2 * h - 1) = wordsVal s.mem B (arr w 18 + 8) (2 * h - 1) := by
    rw [tm, wvw _ (by omega_using []) (by omega_using [hnw, f18]) (by omega_using [hw, hnw, f18]),
      (writeW32_outside s.mem B (d := 92) _ (by omega_using [])).wordsVal (by omega_using [h18]) (by omega_using [hw, hnw, f18])]
  have hX' := hX
  rw [show 2 * h = (2 * h - 1) + 1 by omega_using [h2], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low] at hX'
  refine ⟨?_, ?_, ?_, ?_, hW2.of_keep tk, ((uk.trans vk).trans tk).mono (by decide)⟩
  · rw [show 2 * h = (2 * h - 1) + 1 by omega_using [h2], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, hup, tm,
      word_writeW_self, BitVec.toNat_or, hz]
    by_cases h0 : X = 0
    · simp only [h0, ↓reduceIte] at hX' ⊢
      have w0 : (Mont.word s.mem B (arr w 18)).toNat = 0 := by omega_using [hX']
      have u0 : wordsVal s.mem B (arr w 18 + 8) (2 * h - 1) = 0 := by omega_using [hX']
      rw [w0, u0]; rfl
    · simp only [h0, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero]
      omega_using [hX']
  · rw [tm, show slot _ B 92 = Mont.w32 _ B 92 from rfl,
      (writeW_outside _ B (d := arr w 18) _ (by omega_using [hnw, f18])).w32 (by omega_using [h18]) (by omega_using []),
      ← show slot _ B 92 = Mont.w32 _ B 92 from rfl, VG.Proof.Rsa.PPC64LE.Keys.slot_write_self]
    split <;> rfl
  · rw [tm]
    exact writeW_outside _ B _ (by omega_using [hnw, f18])
  · rw [tm]
    exact (VG.Proof.Rsa.PPC64LE.Keys.keep_slot (d := 92) _ _ (by simp) (by omega_using [])).trans
      (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 18) (d := 0) (n := 8)
        (by rw [Nat.add_zero]; exact writeW_outside _ B _ (by omega_using [hnw, f18])) (by simp only [S]; omega_using []) (by simp))

/-- `clzX`: the leading zero words `r` (`r10`) of `X` (`2 h` words) and its top word that is not zero (`r11`). -/
theorem clzX_ok {s : State} {B : Addr} {Z w N h : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hw : w = 4 * h + 6)
    (h2 : 2 ≤ h) (hh : h < 2 ^ 20) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.clzX s fun t =>
      (∃ r, t.gpr .r10 = BitVec.ofNat 64 r ∧ VG.Proof.Rsa.PPC64LE.RdShift.ClzOf (wordsVal s.mem B (arr w 18) (2 * h))
        (2 * h) r ∧ (t.gpr .r11).toNat = topW (wordsVal s.mem B (arr w 18) (2 * h)) (2 * h) r) ∧
      t.mem = s.mem ∧ Ws t B Z w N ∧ Keep [.r0, .r3, .r5, .r8, .r9, .r10, .r11] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  simp only [S] at f18
  have h18 : 160 ≤ arr w 18 := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr _
  have pv : BitVec.ofNat 64 18 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 18) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 18 (S w)
  have e5 : off B (arr w 18) + BitVec.ofNat 64 (2 * h) <<< 3 - 8#64 = off B (arr w 18 + 8 * (2 * h) - 8) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.shl3_val, off_add, show (8#64) = BitVec.ofNat 64 8 from rfl,
      VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega_using [h2])]
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.clzX
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.mono (WP.keep [.r0, .r5, .r8, .r9, .r10, .r11] (Q := fun u =>
      u.gpr .r5 = off B (arr w 18 + 8 * (2 * h) - 8) ∧ u.gpr .r8 = BitVec.ofNat 64 (2 * h) ∧
      u.gpr .r9 = BitVec.allOnes 64 ∧ u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.gpr .r11 = BitVec.ofNat 64 0 ∧
      u.mem = s.mem) (by
    mcrun [pv, e5, VG.Impl.Rsa.PPC64LE.RecoverDet.twoH, VG.Impl.Rsa.PPC64LE.RecoverDet.wR, KeyWorkspace.hdr,
      VG.Impl.Rsa.PPC64LE.Keys.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r29, hW.r30, hW.r31, twoH_val hw hh,
      BitVec.add_zero]
    decide) (by decide)) fun u ⟨⟨u5, u8, u9, u10, u11, um⟩, uk⟩ => ?_)
  refine WP.mono (clzXScan_ok (hs.congr uk.wr) u5 u8 u9 u10 u11 (by omega_using [h2]) (by omega_using [hh]) (by omega_using [h18]) (by omega_using [hw, f18]))
    fun t ⟨tr, tm, tk⟩ => ?_
  rw [um] at tr tm
  exact ⟨tr, tm, hW.of_keep (uk.trans tk), (uk.trans tk).mono (by decide)⟩

/-- `remZero`: `sOk5 :=` whether `X'`'s `2 h` words are zero. -/
theorem remZero_ok {s : State} {B : Addr} {Z w N h : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hw : w = 4 * h + 6)
    (h2 : 2 ≤ h) (hh : h < 2 ^ 20) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.remZero s fun t =>
      slot t.mem B VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5 =
        (if wordsVal s.mem B (arr w 18) (2 * h) = 0 then 1 else 0) ∧
      t.mem = s.mem.writeW (off B VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5)
        (BitVec.ofNat 32 (if wordsVal s.mem B (arr w 18) (2 * h) = 0 then 1 else 0)) ∧
      Ws t B Z w N ∧ Keep [.r0, .r3, .r5, .r8, .r9, .r11] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  simp only [S] at f18
  have hz160 : 160 ≤ Z := hW.hdr_le
  have pv : BitVec.ofNat 64 18 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 18) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 18 (S w)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.remZero
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine WP.seq (WP.mono (WP.keep [.r5, .r8, .r9, .r11] (Q := fun u => u.gpr .r5 = off B (arr w 18) ∧
      u.gpr .r8 = BitVec.ofNat 64 (2 * h) ∧ u.gpr .r9 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) (by
    mcrun [pv, VG.Impl.Rsa.PPC64LE.RecoverDet.twoH, VG.Impl.Rsa.PPC64LE.RecoverDet.wR, KeyWorkspace.hdr,
      VG.Impl.Rsa.PPC64LE.Keys.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r29,
      hW.r30, hW.r31, twoH_val hw hh, BitVec.add_zero]) (by decide)) fun u ⟨⟨u5, u8, u9, um⟩, uk⟩ => ?_)
  refine WP.seq (WP.mono (orLoop_ok (hs.congr uk.wr) u5 u8 u9 (by omega_using [h2]) (by omega_using [hh]) (by omega_using [hw, f18]))
    fun v ⟨v9, vm, vk⟩ => ?_)
  rw [um] at v9
  have hW2 := hW.of_keep (uk.trans vk)
  obtain ⟨z, hz⟩ : ∃ z : Nat, z = if wordsVal s.mem B (arr w 18) (2 * h) = 0 then 1 else 0 := ⟨_, rfl⟩
  have e3 : (0#64 - v.gpr .r9 ||| v.gpr .r9) >>> 63 ^^^ 1#64 = BitVec.ofNat 64 z := by
    rw [BitVec.or_comm, VG.Proof.Rsa.PPC64LE.RdShift.nz_bit, hz]
    by_cases h0 : v.gpr .r9 = 0#64
    · simp only [h0, ↓reduceIte, v9.mp h0]; rfl
    · have : wordsVal s.mem B (arr w 18) (2 * h) ≠ 0 := fun e => h0 (v9.mpr e)
      simp only [h0, this, ↓reduceIte]; rfl
  have ez : (BitVec.ofNat 64 z).setWidth 32 = BitVec.ofNat 32 z := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [hz]; split <;> rfl
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun t => t.mem = v.mem.writeW (off B 48) (BitVec.ofNat 32 z)) (by
    mcrun [e3, ez, hW2.r31, VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5, hW2.scr.st (show 48 + 4 ≤ Z by omega_using [hz160]),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show 48 < 2 ^ 15 by decide)]) (by decide)) fun t ⟨tm, tk⟩ => ?_
  rw [vm, um, hz] at tm
  refine ⟨?_, tm, hW2.of_keep tk, ((uk.trans vk).trans tk).mono (by decide)⟩
  rw [tm, show VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5 = 48 from rfl, VG.Proof.Rsa.PPC64LE.Keys.slot_write_self]
  split <;> rfl

/-- `rootFix`: the root's word 0 less the slot `sZ`. -/
theorem rootFix_ok {s : State} {B : Addr} {Z w N : Nat} (hW : Ws s B Z w N) (hN : 2 < N) {z : Nat}
    (hz : slot s.mem B VG.Impl.Rsa.PPC64LE.RecoverDet.sZ = z) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.RecoverDet.rootFix) s fun t =>
      t.mem = s.mem.writeW (off B (arr w 2)) (Mont.word s.mem B (arr w 2) - BitVec.ofNat 64 z) ∧
      Ws t B Z w N ∧ Keep [.r0, .r3, .r5] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have f2 := hW.arr_fit (j := 2) hN
  simp only [S] at f2
  have hz160 : 160 ≤ Z := hW.hdr_le
  have pv : BitVec.ofNat 64 2 * BitVec.ofNat 64 (S w) + B + 160#64 = off B (arr w 2) :=
    VG.Proof.Rsa.PPC64LE.Keys.ptr_val B 2 (S w)
  refine WP.mono (WP.keep [.r0, .r3, .r5] (Q := fun t => t.mem = s.mem.writeW (off B (arr w 2))
      (Mont.word s.mem B (arr w 2) - BitVec.ofNat 64 z)) (by
    mcrun [pv, VG.Impl.Rsa.PPC64LE.RecoverDet.rootFix, VG.Impl.Rsa.PPC64LE.RecoverDet.wS, KeyWorkspace.hdr,
      VG.Impl.Rsa.PPC64LE.Keys.hdr, VG.Impl.Rsa.PPC64LE.Keys.ptr, hW.r30, hW.r31,
      VG.Impl.Rsa.PPC64LE.RecoverDet.sZ, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show 92 < 2 ^ 15 by decide),
      hs.ld (d := 92) (n := 4) (by omega_using [hz160]), hs.ld (show arr w 2 + 8 ≤ Z by omega_using [f2]), hs.st (show arr w 2 + 8 ≤ Z by omega_using [f2])]
    have lz : (s.mem.readW (B + 92#64) 32).setWidth 64 = BitVec.ofNat 64 z :=
      VG.Proof.Rsa.PPC64LE.Recover.ld_slot (d := 92) hz
    rw [lz]) (by decide)) fun t ⟨tm, tk⟩ => ⟨tm, hW.of_keep tk, tk⟩

end ZeroX

/-! ## Before the steps -/

section SqrtPre
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S slot num)
open VG.Proof.Rsa.PPC64LE.RdShift (ClzOf num_words)

/-- Equal arrays have equal low words. -/
theorem wv_of_num {m m' : Mem} {B : Addr} {w L k j : Nat} (hw : w = 2 * L) (hk : k ≤ L)
    (h : num m' B w j = num m B w j) : wordsVal m' B (arr w j) k = wordsVal m B (arr w j) k := by
  rw [num_words _ _ _ hw, num_words _ _ _ hw] at h
  have sp := fun (mm : Mem) => VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append mm B (arr w j) k (L - k)
  rw [show k + (L - k) = L by omega_using [hk]] at sp
  have l1 := wordsVal_lt m' B (arr w j) k
  have l2 := wordsVal_lt m B (arr w j) k
  have := congrArg (· % 2 ^ (64 * k)) h
  simp only [sp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
  exact this

/-- `copy`, `zeroX`, `clzX` and the counts: `D := 0`, `X₁ = X` (or 1 if `X = 0`) in `X'`'s `2 h` words, its
leading zero words `r` and its top word's leading zero bits `cb`, in the slots. -/
theorem sqrtPreA_ok {s : State} {B : Addr} {Z w N h X X1 : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hN' : N ≤ 256)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (hz15 : num s.mem B w 15 = 0)
    (eX : X = wordsVal s.mem B (arr w 18) (2 * h)) (eX1 : X1 = if X = 0 then 1 else X) :
    WP isa (.seq (VG.Impl.Rsa.PPC64LE.Keys.copy 2 15) (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.zeroX
      (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.clzX (.block VG.Impl.Rsa.PPC64LE.RecoverDet.counts)))) s fun t =>
      wordsVal t.mem B (arr w 18) (2 * h) = X1 ∧ num t.mem B w 2 = 0 ∧
      (∃ r cb, ClzOf X1 (2 * h) r ∧ 2 ^ 63 ≤ topW X1 (2 * h) r * 2 ^ cb ∧ topW X1 (2 * h) r * 2 ^ cb < 2 ^ 64 ∧
        cb < 64 ∧ slot t.mem B 76 = r ∧ slot t.mem B 80 = cb / 2 * 2 ∧
        slot t.mem B 84 = ((64 * r + cb) / 2 + 1) / 64 ∧ slot t.mem B 88 = ((64 * r + cb) / 2 + 1) % 64) ∧
      slot t.mem B 92 = (if X = 0 then 1 else 0) ∧ Ws t B Z w N ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2] [92, 76, 80, 84, 88] s.mem t.mem ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t := by
  have hs := hW.scr
  have hnw := hs.nowrap
  have hL : w = 2 * (2 * h + 3) := by omega_using [hw]
  refine WP.seq (WP.mono (VG.Proof.Rsa.PPC64LE.Keys.copy_ok hW (o := 2) (a := 15) (by omega_using [hN]) (by omega_using [hN]) hN'
    (by decide)) fun t1 ⟨W1, k1, n1, r1, _⟩ => ?_)
  have x1 : wordsVal t1.mem B (arr w 18) (2 * h) = X := by
    rw [eX]; exact wv_of_num hL (by omega_using []) (k1.num (by decide) (by decide) (W1.fit64 (by omega_using [hN])))
  refine WP.seq (WP.mono (zeroX_ok W1 hN hw h2 hh x1) fun t2 ⟨z1, z2, _, k2, W2, r2⟩ => ?_)
  rw [← eX1] at z1
  have n2 : num t2.mem B w 2 = 0 := by
    rw [k2.num (by decide) (by decide) (W2.fit64 (by omega_using [hN])), n1, hz15]
  refine WP.seq (WP.mono (clzX_ok W2 hN hw h2 hh) fun t3 ⟨⟨r, c10, cc, c11⟩, m3, W3, r3⟩ => ?_)
  rw [z1] at cc c11
  have hX1 : X1 ≠ 0 := by rw [eX1]; split <;> omega_arith
  have tlt : topW X1 (2 * h) r < 2 ^ 64 := by
    obtain ⟨-, -, c3⟩ := cc
    obtain ⟨lo, hi⟩ := c3 hX1
    simp only [topW, hX1, ↓reduceIte]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    have : r + 1 ≤ 2 * h := by
      refine Nat.lt_of_not_le fun h' => ?_
      rw [show 2 * h - r = 0 by omega_using [h'], Nat.mul_zero, Nat.pow_zero] at hi; omega_arith
    rwa [show 64 + 64 * (2 * h - r - 1) = 64 * (2 * h - r) by omega_using [this]]
  have tpos : 0 < topW X1 (2 * h) r := by
    obtain ⟨-, -, c3⟩ := cc
    obtain ⟨lo, hi⟩ := c3 hX1
    simp only [topW, hX1, ↓reduceIte]
    exact Nat.div_pos lo (Nat.two_pow_pos _)
  have hr : r < 2 ^ 21 := by have := cc.1; omega_using [hh, this]
  refine WP.mono (counts_ok W3 c10 (by rw [← c11]; simp) hr tpos tlt)
    fun t ⟨⟨cb, b1, b2, b3, s1, s2, s3, s4⟩, k4, sz4, r4⟩ => ?_
  refine ⟨?_, ?_, ⟨r, cb, cc, b1, b2, b3, s1, s2, s3, s4⟩, ?_, W3.of_keep r4, ?_, ?_⟩
  · rw [← z1, ← m3]; exact wv_of_num hL (by omega_using []) (k4.num (by decide) (by decide) (W3.fit64 (by omega_using [hN])))
  · rw [k4.num (by decide) (by decide) (W3.fit64 (by omega_using [hN])), m3, n2]
  · rw [sz4, m3]; exact z2
  · rw [← m3] at k2
    exact (((k1.mono (by decide) (by decide)).trans (k2.mono (by decide) (by decide))).trans
      (k4.mono (by decide) (by decide)))
  · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)

/-- The low `k` words of `L`. -/
theorem wv_low (m : Mem) (B : Addr) {d k L : Nat} (hk : k ≤ L) :
    wordsVal m B d k = wordsVal m B d L % 2 ^ (64 * k) := by
  have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append m B d k (L - k)
  rw [show k + (L - k) = L by omega_using [hk]] at sp
  rw [sp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

theorem seq_assoc_iff {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := by
  constructor
  · intro h; rw [WP.seq_iff] at h; rw [WP.seq_iff, WP.seq_iff]; exact WP.mono h fun t ht => WP.seq_iff.mp ht
  · intro h; rw [WP.seq_iff, WP.seq_iff] at h; rw [WP.seq_iff]; exact WP.mono h fun t ht => WP.seq_iff.mpr ht

/-- Before the steps: `X₁ = X` (or 1) shifted up by `2 c` into `X'`'s `2 h` words, its top two words at least
`2^126`; `D = 0`; the slots `sZ`, and `sRw`, `sRb` the words and bits of `c + 1`. -/
theorem sqrtPre_ok {s : State} {B : Addr} {Z w N h X X1 : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hN' : N ≤ 256)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (hz15 : num s.mem B w 15 = 0)
    (eX : X = wordsVal s.mem B (arr w 18) (2 * h)) (eX1 : X1 = if X = 0 then 1 else X) :
    WP isa (.seq (.seq (VG.Impl.Rsa.PPC64LE.Keys.copy 2 15) (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.zeroX
      (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.clzX (.block VG.Impl.Rsa.PPC64LE.RecoverDet.counts))))
      (VG.Impl.Rsa.PPC64LE.RecoverDet.shlBy 18 76 80 true)) s fun t =>
      ∃ c, wordsVal t.mem B (arr w 18) (2 * h) = X1 * 4 ^ c ∧ X1 * 4 ^ c < 2 ^ (64 * (2 * h)) ∧
        2 ^ 126 ≤ X1 * 4 ^ c / 2 ^ (64 * (2 * h - 2)) ∧ num t.mem B w 2 = 0 ∧
        slot t.mem B 92 = (if X = 0 then 1 else 0) ∧ slot t.mem B 84 = (c + 1) / 64 ∧ slot t.mem B 88 = (c + 1) % 64 ∧
        c < 64 * h ∧ Ws t B Z w N ∧
        VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2] [92, 76, 80, 84, 88] s.mem t.mem ∧
        Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t := by
  have hL : w = 2 * (2 * h + 3) := by omega_using [hw]
  rw [WP.seq_iff]
  refine WP.mono (sqrtPreA_ok hW hN hN' hw h2 hh hz15 eX eX1)
    fun u ⟨u18, u2, ⟨r, cb, cc, b1, b2, b3, s1, s2, s3, s4⟩, sz, Wu, ku, ru⟩ => ?_
  have hX1 : X1 ≠ 0 := by rw [eX1]; split <;> omega_arith
  obtain ⟨nb1, nb2⟩ := norm_bounds (show 2 ≤ 2 * h by omega_using [h2]) hX1 cc b1 b2
  have hr : r < 2 * h := by
    obtain ⟨c1, -, c3⟩ := cc
    obtain ⟨lo, hi⟩ := c3 hX1
    refine Nat.lt_of_not_le fun h' => ?_
    rw [show 2 * h - r = 0 by omega_using [h'], Nat.mul_zero, Nat.pow_zero] at hi; omega_using [hN, hN', hw, h2, hh, hz15, eX, eX1, hL, u18, u2, b1, b2, b3, s1, s2, s3, s4, sz, hX1, nb1, nb2, c1, c3, lo, hi, h']
  refine WP.mono (VG.Proof.Rsa.PPC64LE.RdShift.shlBy_ok (L := 2 * h + 3) true Wu (j := 18) hN hN' hL (by omega_using [])
    (by decide) (by decide) s1 s2 (by omega_using [hr]) (fun _ => by omega_using [b3])) fun t ⟨v, o, Wt, kt⟩ => ?_
  have hs := Wu.scr
  have hnw := hs.nowrap
  have f18 := Wu.arr_fit (j := 18) (by omega_using [hN])
  have f2 := Wu.arr_fit (j := 2) (by omega_using [hN])
  have a218 : arr w 2 + S w ≤ arr w 18 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  have h160 : 160 ≤ arr w 2 := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr _
  simp only [S] at f18 f2 a218
  have e4 : 4 ^ (32 * r + cb / 2) = 2 ^ (64 * r + cb / 2 * 2) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega_using []
  refine ⟨32 * r + cb / 2, ?_, by rw [e4]; exact nb1, by rw [e4]; exact nb2, ?_, ?_, ?_, ?_, by omega_using [b3, hr], Wt, ?_,
    (ru.trans kt).mono (by decide)⟩
  · rw [wv_low t.mem B (k := 2 * h) (L := 2 * h + 3) (by omega_using []), v]
    simp only [↓reduceIte]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using []))]
    have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append u.mem B (arr w 18) (2 * h) 3
    rw [sp, u18, Nat.add_mul, Nat.mul_assoc, Nat.add_mul_mod_self_left, e4, Nat.mod_eq_of_lt nb1]
  · rw [VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ hL, o.wordsVal (by omega_using [hw, a218]) (by omega_using [hw, hnw, f2]),
      ← VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ hL, u2]
  · rw [show slot t.mem B 92 = Mont.w32 t.mem B 92 from rfl, o.w32 (by omega_using [a218, h160]) (by omega_using [])]; exact sz
  · rw [show slot t.mem B 84 = Mont.w32 t.mem B 84 from rfl, o.w32 (by omega_using [a218, h160]) (by omega_using [])]
    exact s3.trans (by congr 2; omega_using [])
  · rw [show slot t.mem B 88 = Mont.w32 t.mem B 88 from rfl, o.w32 (by omega_using [a218, h160]) (by omega_using [])]
    exact s4.trans (by congr 2; omega_using [])
  · exact ku.trans (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 18) (d := 0) (by rw [Nat.add_zero]; exact o)
      (by simp only [S]; omega_using [hw]) (by simp))

end SqrtPre

/-! ## After the steps -/

section SqrtPost
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S slot num)
open VG.Spec.Rsa (isqrt)

/-- The root's math: `s` the root of `Y = 4^c X₁` with remainder `r`, `X₁ = X` or 1 for `X = 0`: `X`'s root is
`2 s / 2^(c+1)` less one for `X = 0`, and `X` is a square exactly where `r = 0`. -/
theorem post_math {X X1 c s r : Nat} (eX1 : X1 = if X = 0 then 1 else X) (h : s * s + r = X1 * 4 ^ c)
    (hr : r ≤ 2 * s) :
    2 * s / 2 ^ (c + 1) - (if X = 0 then 1 else 0) = isqrt X ∧
      (r = 0 ↔ isqrt X * isqrt X = X) ∧ (if X = 0 then 1 else 0) ≤ 2 * s / 2 ^ (c + 1) := by
  have h' : s * s + r = 4 ^ c * X1 := by rw [h, Nat.mul_comm]
  have hs := VG.Proof.Bignum.SqrtRem.sqrt_of_rem h' hr
  have ns := VG.Proof.Bignum.SqrtRem.norm_sqrt c X1
  have nq := VG.Proof.Bignum.SqrtRem.norm_square c X1
  have sq := VG.Proof.Bignum.SqrtRem.square_iff_rem h' hr
  rw [hs] at ns nq sq
  have e2 : 2 * s / 2 ^ (c + 1) = s / 2 ^ c := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ c), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by decide)]
  rw [e2, ns]
  by_cases h0 : X = 0
  · subst h0
    simp only [↓reduceIte] at eX1 ⊢
    subst eX1
    have i1 : isqrt 1 = 1 := VG.Proof.Rsa.RecoverDet.isqrt_eq (by decide) (by decide)
    have i0 : isqrt 0 = 0 := VG.Proof.Rsa.RecoverDet.isqrt_eq (by decide) (by decide)
    rw [i1, i0]
    exact ⟨rfl, ⟨fun _ => rfl, fun _ => (sq.symm.trans nq).mpr (by rw [i1])⟩, le_refl _⟩
  · simp only [h0, ↓reduceIte] at eX1 ⊢
    subst eX1
    exact ⟨Nat.sub_zero _, sq.symm.trans nq, Nat.zero_le _⟩

/-- After the steps: `sOk5 :=` whether the remainder is zero, `D := D / 2^(c+1)` and less `sZ`: the root of `X`
and whether it is a square. -/
theorem sqrtPost_ok {u : State} {B : Addr} {Z w N h X X1 Y c s : Nat} (I : RdSqrtW.SqInv u B Z w N h Y s h)
    (hN' : N ≤ 256) (eX1 : X1 = if X = 0 then 1 else X) (eY : Y = X1 * 4 ^ c) (hc : c < 64 * h)
    (s92 : slot u.mem B 92 = (if X = 0 then 1 else 0)) (s84 : slot u.mem B 84 = (c + 1) / 64)
    (s88 : slot u.mem B 88 = (c + 1) % 64) :
    WP isa (.seq VG.Impl.Rsa.PPC64LE.RecoverDet.remZero (.seq (VG.Impl.Rsa.PPC64LE.RecoverDet.shrBy 2 84 88)
      (.block VG.Impl.Rsa.PPC64LE.RecoverDet.rootFix))) u fun t =>
      wordsVal t.mem B (arr w 2) (2 * h + 3) = isqrt X ∧
      slot t.mem B 48 = (if isqrt X * isqrt X = X then 1 else 0) ∧ Ws t B Z w N ∧
      VG.Proof.Rsa.KeyWorkspace.Keep B w [2] [48] u.mem t.mem ∧
      Keep [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] u t := by
  obtain ⟨hW, hN, hw, h2, hh, _, _, _, _, _, _, sq, sr, _, _, _, rem, dv, _, _, _, hi, dhi⟩ := I
  have hs := hW.scr
  have hnw := hs.nowrap
  have hL : w = 2 * (2 * h + 3) := by omega_using [hw]
  have f18 := hW.arr_fit (j := 18) (by omega_using [hN])
  have f2 := hW.arr_fit (j := 2) (by omega_using [hN])
  have a218 : arr w 2 + S w ≤ arr w 18 := VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)
  have h160 : 160 ≤ arr w 2 := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr _
  simp only [S] at f18 f2 a218
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at sq sr rem dv
  rw [show 2 * h - h + 1 = h + 1 by omega_using []] at hi
  -- The remainder in `X'`'s `2 h` words, `2 s` in `D`'s.
  have eR : wordsVal u.mem B (arr w 18) (2 * h) = Y - s * s := by
    rw [show 2 * h = (h + 1) + (h - 1) by omega_using [hc], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, rem, hi]; simp
  have eD : wordsVal u.mem B (arr w 2) (2 * h + 3) = 2 * s := by
    rw [show 2 * h + 3 = (h + 1) + (h + 2) by omega_using [], VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append, dv, dhi]; simp
  have hm := post_math eX1 (show s * s + (Y - s * s) = X1 * 4 ^ c by omega_using [eY, sq]) sr
  refine WP.seq (WP.mono (remZero_ok hW hN hw h2 hh) fun v ⟨z1, zm, Wv, kv⟩ => ?_)
  rw [eR] at z1 zm
  simp only [VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5] at zm z1
  obtain ⟨hm1, hm2, hm3⟩ := hm
  have eDv : wordsVal v.mem B (arr w 2) (2 * h + 3) = 2 * s := by
    rw [zm, (writeW32_outside u.mem B (d := 48) _ (by omega_using [])).wordsVal (d := arr w 2) (k := 2 * h + 3) (by omega_using [h160])
      (by omega_using [hw, hnw, f2]), eD]
  have sw := fun (e : Nat) (he : e = 84 ∨ e = 88 ∨ e = 92) =>
    VG.Proof.Rsa.PPC64LE.Recover.slot_wne u.mem B (d := 48) (e := e)
      (BitVec.ofNat 32 (if Y - s * s = 0 then 1 else 0)) (by omega_using [he]) (by omega_using []) (by omega_using [he])
  have v84 : slot v.mem B 84 = (c + 1) / 64 := by rw [zm, sw 84 (by omega_using []), s84]
  have v88 : slot v.mem B 88 = (c + 1) % 64 := by rw [zm, sw 88 (by omega_using []), s88]
  have v92 : slot v.mem B 92 = (if X = 0 then 1 else 0) := by rw [zm, sw 92 (by omega_using []), s92]
  refine WP.seq (WP.mono (VG.Proof.Rsa.PPC64LE.RdShift.shrBy_ok (L := 2 * h + 3) Wv (j := 2) (by omega_using [hN]) hN' hL
    (by omega_using []) (by decide) (by decide) v84 v88 (by omega_using [hc]) (Nat.mod_lt _ (by decide)))
    fun t1 ⟨r1, o1, W1, k1⟩ => ?_)
  rw [eDv, show 64 * ((c + 1) / 64) + (c + 1) % 64 = c + 1 by omega_using []] at r1
  have t92 : slot t1.mem B 92 = (if X = 0 then 1 else 0) := by
    rw [show slot t1.mem B 92 = Mont.w32 t1.mem B 92 from rfl, o1.w32 (by omega_using [h160]) (by omega_using [])]; exact v92
  refine WP.mono (rootFix_ok W1 (by omega_using [hN]) t92) fun t ⟨tm, Wt, kt⟩ => ⟨?_, ?_, Wt, ?_,
    ((kv.trans k1).trans kt).mono (rs' := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]) (by decide)⟩
  · rw [tm, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low, word_writeW_self,
      (writeW_outside t1.mem B (d := arr w 2) _ (by omega_using [hnw, f2])).wordsVal (by omega_using []) (by omega_using [hw, hnw, f2])]
    rw [show 2 * h + 3 = (2 * h + 2) + 1 from rfl, VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low] at r1
    rw [← hm1]
    have hw0 := (Mont.word t1.mem B (arr w 2)).isLt
    generalize hV : 2 * s / 2 ^ (c + 1) = V at r1 hm3 hm1 ⊢
    by_cases h0 : X = 0
    · simp only [h0, ↓reduceIte] at hm3 hm1 ⊢
      have i0 : isqrt 0 = 0 := VG.Proof.Rsa.RecoverDet.isqrt_eq (by decide) (by decide)
      rw [i0] at hm1
      have hw1 : (Mont.word t1.mem B (arr w 2)).toNat = 1 := by
        have := Nat.mul_le_mul_left (2 ^ 64) (show 0 ≤ wordsVal t1.mem B (arr w 2 + 8) (2 * h + 2) from Nat.zero_le _)
        rcases Nat.eq_zero_or_pos (wordsVal t1.mem B (arr w 2 + 8) (2 * h + 2)) with e | e
        · rw [e] at r1; omega_using [r1, hm3, hm1]
        · have := Nat.le_mul_of_pos_right (2 ^ 64) e; omega_using [r1, hm3, hm1]
      have hW0 : wordsVal t1.mem B (arr w 2 + 8) (2 * h + 2) = 0 := by
        rw [hw1] at r1
        rcases Nat.eq_zero_or_pos (wordsVal t1.mem B (arr w 2 + 8) (2 * h + 2)) with e | e
        · exact e
        · have := Nat.le_mul_of_pos_right (2 ^ 64) e; omega_using [r1, hm1]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hw1]; decide), hw1, hW0]
      rw [show (1#64).toNat = 1 from rfl]; omega_using [hm1]
    · simp only [h0, ↓reduceIte, BitVec.sub_zero]
      rw [← r1]; rfl
  · rw [show slot t.mem B 48 = Mont.w32 t.mem B 48 from rfl, tm,
      (writeW_outside t1.mem B (d := arr w 2) _ (by omega_using [hnw, f2])).w32 (by omega_using [h160]) (by omega_using []),
      o1.w32 (by omega_using [h160]) (by omega_using []), ← show slot v.mem B 48 = Mont.w32 v.mem B 48 from rfl, z1]
    simp only [← hm2]
  · rw [tm]
    exact (((show VG.Proof.Rsa.KeyWorkspace.Keep B w [2] [48] u.mem v.mem by
      rw [zm]; exact VG.Proof.Rsa.PPC64LE.Keys.keep_slot (d := 48) _ _ (by simp) (by omega_using []))).trans
      (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 2) (d := 0) (by rw [Nat.add_zero]; exact o1)
        (by simp only [S]; omega_using [hw]) (by simp))).trans
      (VG.Proof.Rsa.KeyWorkspace.Keep.of_arr (o := 2) (d := 0) (n := 8)
        (by rw [Nat.add_zero]; exact writeW_outside _ B _ (by omega_using [hnw, f2])) (by simp only [S]; omega_using []) (by simp))

end SqrtPost

/-! ## The root, by words -/

section SqrtW
open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Proof.Rsa.KeyWorkspace (arr S slot num)
open VG.Spec.Rsa (isqrt)

theorem pre_assoc {a b c d e f : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq (.seq a (.seq b (.seq c d))) e) f) s Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e f))))) s Q := by
  rw [WP.seq_iff, WP.seq_iff, WP.seq_iff] at h
  rw [WP.seq_iff]
  refine WP.mono h fun t1 h1 => ?_
  rw [WP.seq_iff] at h1
  rw [WP.seq_iff]
  refine WP.mono h1 fun t2 h2 => ?_
  rw [WP.seq_iff] at h2
  rw [WP.seq_iff]
  refine WP.mono h2 fun t3 h3 => ?_
  rw [WP.seq_iff]
  refine WP.mono h3 fun t4 h4 => ?_
  rw [WP.seq_iff]
  exact h4

theorem post_assoc {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  rw [WP.seq_iff]
  refine WP.mono h fun t1 h1 => ?_
  rw [WP.seq_iff] at h1
  rw [WP.seq_iff]
  refine WP.mono h1 fun t2 h2 => ?_
  rw [WP.seq_iff]
  exact h2

/-- The root of `X` (`X'`'s `2 h` words) by words, then `ctxw`: `D`'s `2 h + 3` words its root, `sOk5` whether
it is a square. -/
theorem sqrtW_ok {s : State} {B : Addr} {Z w N h X : Nat} (hW : Ws s B Z w N) (hN : 18 < N) (hN' : N ≤ 256)
    (hw : w = 4 * h + 6) (h2 : 2 ≤ h) (hh : h < 2 ^ 20) (hz15 : num s.mem B w 15 = 0)
    (eX : X = wordsVal s.mem B (arr w 18) (2 * h)) {Q : State → Prop}
    (k : ∀ t, wordsVal t.mem B (arr w 2) (2 * h + 3) = isqrt X →
      slot t.mem B 48 = (if isqrt X * isqrt X = X then 1 else 0) → Ws t B Z w N →
      VG.Proof.Rsa.KeyWorkspace.Keep B w [18, 2, 3] [92, 76, 80, 84, 88, 48] s.mem t.mem →
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
        .r22, .r24, .r26, .r28] s t →
      WP isa (.block VG.Impl.Rsa.PPC64LE.Recover.ctxw) t Q) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.sqrt s Q := by
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.sqrt
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  refine pre_assoc ?_
  rw [WP.seq_iff]
  refine WP.mono (sqrtPre_ok hW hN hN' hw h2 hh hz15 eX rfl)
    fun u ⟨c, u18, ulti, uT, u2, s92, s84, s88, hc, Wu, ku, ru⟩ => ?_
  -- `D`'s words are zero.
  have hL : w = 2 * (2 * h + 3) := by omega_using [hw]
  have eD0 : wordsVal u.mem B (arr w 2) (2 * h + 3) = 0 := by
    rw [← VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ hL]; exact u2
  have hz : wordsVal u.mem B (arr w 2) (h - 1) = 0 := by
    rw [wv_low u.mem B (L := 2 * h + 3) (by omega_using []), eD0]; rfl
  have hzh : wordsVal u.mem B (arr w 2 + 8 * (h + 1)) (h + 2) = 0 := by
    have sp := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append u.mem B (arr w 2) (h + 1) (h + 2)
    rw [show h + 1 + (h + 2) = 2 * h + 3 by omega_using [], eD0] at sp
    have := Nat.two_pow_pos (64 * (h + 1))
    rcases Nat.eq_zero_or_pos (wordsVal u.mem B (arr w 2 + 8 * (h + 1)) (h + 2)) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * (h + 1))) e; omega_arith
  rw [seq_assoc_iff, WP.seq_iff]
  refine WP.mono (first_ok Wu hN hw h2 hh u18 uT hz hzh) fun v ⟨⟨sv, Iv⟩, kv, rv⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (steps_ok Iv) fun t1 ⟨⟨s1, I1⟩, k1, r1⟩ => ?_
  have slt : ∀ e, e = 92 ∨ e = 84 ∨ e = 88 → slot t1.mem B e = slot u.mem B e := fun e he => by
    rw [k1.slot (by rcases he with rfl | rfl | rfl <;> decide) (by simp),
      kv.slot (by rcases he with rfl | rfl | rfl <;> decide) (by simp)]
  refine post_assoc (WP.seq_iff.mpr (WP.mono (sqrtPost_ok (X := X) I1 hN' rfl rfl hc
    (by rw [slt 92 (by simp)]; exact s92) (by rw [slt 84 (by simp)]; exact s84) (by rw [slt 88 (by simp)]; exact s88))
    fun t ⟨e1, e2, Wt, kt, rt⟩ => k t e1 e2 Wt ?_ ?_))
  · exact (((ku.mono (by decide) (by decide)).trans (kv.mono (by decide) (by decide))).trans
      (k1.mono (by decide) (by decide))).trans (kt.mono (by decide) (by decide))
  · exact (((ru.trans rv).trans r1).trans rt).mono (by decide)

end SqrtW

end VG.Proof.Rsa.PPC64LE.RdSqrtW
