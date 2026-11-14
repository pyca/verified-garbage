module

public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.GCD.Basic

-- separate module: target-independent, for every architecture's `recover_primes_det` by words

/-!
# Appendix C.2 by words and stages: the model's values in closed form

What `RecoverDet` computes by words and stages (`Impl/Rsa/X86_64/RecoverDet.lean`
documents the method) against the bit-serial model (`RecoverDetModel.lean`),
independent of the target:

* the halvings' result in closed form (`twos_closed`): from `(N, x₂, x₃)`
  with `0 < N < 2^k`, `N / 2^(tz N)`, `x₂ / 2^t` and `x₃ 2^t mod 2^b` for
  `t = tz (gcd N x₂)`, which is what shifts by the stages of
  `ShiftStages` give;
* `model_correct` with the division's quotient and remainder needed only
  where `m < n`, as a division by words of a divisor that only then fits
  gives them (`model_correct_lt`);
* the square root by bit pairs from the top (`pair_succ`, `pair_word`) and the
  words each step needs (`pair_len`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt recoverDet)
open VG.Proof.Bignum.ShiftStages

/-! ## The halvings in closed form -/

/-- After `i` halvings from `(N, x₂, x₃)`. -/
theorem twos_at {b N x₂ x₃ : Nat} (pos : 0 < N) (hx₃ : x₃ < 2 ^ b) : ∀ i,
    (twoStep b)^[i] (N, x₂, x₃) = (N / 2 ^ min i (tz N), x₂ / 2 ^ min i (tz (Nat.gcd N x₂)),
      x₃ * 2 ^ min i (tz (Nat.gcd N x₂)) % 2 ^ b)
  | 0 => by simp [Nat.mod_eq_of_lt hx₃]
  | i + 1 => by
    rw [Function.iterate_succ_apply', twos_at pos hx₃ i]
    have hN0 : N ≠ 0 := by omega_using [pos]
    have hg0 : Nat.gcd N x₂ ≠ 0 := Nat.gcd_ne_zero_left hN0
    have tle : tz (Nat.gcd N x₂) ≤ tz N := (dvd_iff hN0 _).mp
      (Nat.dvd_trans ((dvd_iff hg0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left N x₂))
    generalize ht : tz (Nat.gcd N x₂) = t at tle
    unfold twoStep
    simp only
    by_cases hi : i < tz N
    · -- `u` even.
      have ue : N / 2 ^ min i (tz N) % 2 = 0 := by
        rw [Nat.min_eq_left (by omega_using [hi]), ← Nat.pow_one 2, stage_tz hN0 (by omega_using [hi])]; omega_using [hi]
      simp only [ue, ↓reduceIte]
      by_cases hj : i < t
      · -- both even.
        have hd : 2 ^ (i + 1) ∣ x₂ := Nat.dvd_trans ((dvd_iff hg0 _).mpr (by omega_using [ht, hj])) (Nat.gcd_dvd_right N x₂)
        have xe : x₂ / 2 ^ min i t % 2 = 0 := by
          rw [Nat.min_eq_left (by omega_using [hj])]
          obtain ⟨c, hc⟩ := hd
          rw [hc, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]; omega_using []
        simp only [xe, ↓reduceIte]
        rw [Nat.min_eq_left (show i + 1 ≤ tz N by omega_using [hi]), Nat.min_eq_left (show i + 1 ≤ t by omega_using [hj]),
          Nat.min_eq_left (show i ≤ tz N by omega_using [hi]), Nat.min_eq_left (show i ≤ t by omega_using [hj])]
        simp only [Prod.mk.injEq]
        refine ⟨by rw [Nat.div_div_eq_div_mul, Nat.pow_succ], by rw [Nat.div_div_eq_div_mul, Nat.pow_succ], ?_⟩
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1; rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 2 (2 ^ i)]
      · -- `x₂` odd: `t` is its trailing zeros.
        have hx0 : x₂ ≠ 0 := by
          rintro rfl; rw [Nat.gcd_zero_right] at ht; omega_using [hi, hj, ht]
        have tx : t = tz x₂ := by
          rw [← ht]
          apply Nat.le_antisymm
          · exact (dvd_iff hx0 _).mp (Nat.dvd_trans ((dvd_iff hg0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_right N x₂))
          · refine (dvd_iff hg0 _).mp (Nat.dvd_gcd ((dvd_iff hN0 _).mpr ?_) ((dvd_iff hx0 _).mpr (Nat.le_refl _)))
            -- `tz x₂ ≤ tz N`: else `2^(t + 1)` divides both.
            by_contra c
            have : 2 ^ (t + 1) ∣ Nat.gcd N x₂ :=
              Nat.dvd_gcd ((dvd_iff hN0 _).mpr (by omega_using [hi, hj])) ((dvd_iff hx0 _).mpr (by
                have := (dvd_iff hx0 t).mp (Nat.dvd_trans ((dvd_iff hg0 _).mpr (by omega_using [ht])) (Nat.gcd_dvd_right N x₂))
                omega_using [tle, c]))
            have := (dvd_iff hg0 _).mp this
            omega_arith
        have xo : x₂ / 2 ^ min i t % 2 = 1 := by
          rw [Nat.min_eq_right (by omega_using [hj]), tx]; exact (tz_spec x₂ hx0).2
        simp only [show ¬ (x₂ / 2 ^ min i t % 2 = 0) by omega_using [xo], ↓reduceIte]
        rw [Nat.min_eq_left (show i + 1 ≤ tz N by omega_using [hi]), Nat.min_eq_right (show t ≤ i + 1 by omega_using [hj]),
          Nat.min_eq_left (show i ≤ tz N by omega_using [hi]), Nat.min_eq_right (show t ≤ i by omega_using [hj])]
        simp only [Prod.mk.injEq, and_true]
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    · -- `u` odd.
      have uo : N / 2 ^ min i (tz N) % 2 = 1 := by rw [Nat.min_eq_right (by omega_using [hi])]; exact (tz_spec N hN0).2
      simp only [show ¬ (N / 2 ^ min i (tz N) % 2 = 0) by omega_using [uo], ↓reduceIte]
      rw [Nat.min_eq_right (show tz N ≤ i + 1 by omega_using [hi]), Nat.min_eq_right (show t ≤ i + 1 by omega_using [tle, hi]),
        Nat.min_eq_right (show tz N ≤ i by omega_using [hi]), Nat.min_eq_right (show t ≤ i by omega_using [tle, hi])]

/-- The halvings in closed form. -/
theorem twos_closed {b N x₂ x₃ k : Nat} (pos : 0 < N) (hk : N < 2 ^ k) (hx₃ : x₃ < 2 ^ b) :
    (twoStep b)^[k] (N, x₂, x₃) = (N / 2 ^ tz N, x₂ / 2 ^ tz (Nat.gcd N x₂),
      x₃ * 2 ^ tz (Nat.gcd N x₂) % 2 ^ b) := by
  have hN0 : N ≠ 0 := by omega_using [pos]
  have hg0 : Nat.gcd N x₂ ≠ 0 := Nat.gcd_ne_zero_left hN0
  have tle : tz (Nat.gcd N x₂) ≤ tz N := (dvd_iff hN0 _).mp
    (Nat.dvd_trans ((dvd_iff hg0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left N x₂))
  have := tz_lt pos hk
  rw [twos_at pos hx₃ k, Nat.min_eq_right (by omega_using [this]), Nat.min_eq_right (by omega_using [tle, this])]

/-! ## The division where `m < n` -/

/-- `model_correct`, with the division's quotient and remainder only where `m < n`. -/
theorem model_correct_lt {nb wb n e d q rem : Nat} (odd : n % 2 = 1) (three : 3 ≤ n)
    (hn : 8 * (n + 2) ≤ 2 ^ nb) (hde : d * e < 2 ^ nb) (hw : 2 * nb ≤ wb) (hwe : wb % 2 = 0)
    (hdiv : ltOf nb wb n (d * e) = true → 0 < m1Of nb wb n (d * e) →
      q = dOf nb wb n (d * e) / m1Of nb wb n (d * e) ∧ rem = dOf nb wb n (d * e) % m1Of nb wb n (d * e)) :
    result nb wb n (d * e) q rem = recoverDet n e d := by
  by_cases hl : ltOf nb wb n (d * e) = true
  · exact model_correct odd three hn hde hw hwe (hdiv hl)
  · have hl' : ltOf nb wb n (d * e) = false := by simpa using hl
    rw [← model_correct (q := dOf nb wb n (d * e) / m1Of nb wb n (d * e))
      (rem := dOf nb wb n (d * e) % m1Of nb wb n (d * e)) odd three hn hde hw hwe fun _ => ⟨rfl, rfl⟩]
    simp [result, hl']

/-! ## The square root by bit pairs -/

/-- `X`'s top bits from pair `p` on: four times those from `p + 1`, and pair `p`. -/
theorem pair_succ (X p : Nat) : X / 4 ^ p = 4 * (X / 4 ^ (p + 1)) + X / 4 ^ p % 4 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ 4).symm

/-- Pair `p = 32 q + r` of `X`: bits `2 r` and `2 r + 1` of `X`'s word `q`. -/
theorem pair_word (X q r : Nat) (hr : r < 32) :
    X / 4 ^ (32 * q + r) % 4 = X / 2 ^ (64 * q) % 2 ^ 64 / 2 ^ (2 * r) % 4 := by
  have e : (4 : Nat) ^ (32 * q + r) = 2 ^ (64 * q) * 2 ^ (2 * r) := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega_using []
  rw [e, ← Nat.div_div_eq_div_mul]
  generalize X / 2 ^ (64 * q) = Y
  have hK : 2 ^ 64 = 2 ^ (2 * r) * (4 * 2 ^ (62 - 2 * r)) := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hr]
  have hY : Y = Y % 2 ^ 64 + 2 ^ (2 * r) * (4 * (2 ^ (62 - 2 * r) * (Y / 2 ^ 64))) := by
    have := Nat.mod_add_div Y (2 ^ 64)
    generalize Y / 2 ^ 64 = Qy at this ⊢
    generalize Y % 2 ^ 64 = Ry at this ⊢
    rw [hK, Nat.mul_assoc, Nat.mul_assoc] at this
    exact this.symm
  calc Y / 2 ^ (2 * r) % 4
      = (Y % 2 ^ 64 + 2 ^ (2 * r) * (4 * (2 ^ (62 - 2 * r) * (Y / 2 ^ 64)))) / 2 ^ (2 * r) % 4 := by rw [← hY]
    _ = Y % 2 ^ 64 / 2 ^ (2 * r) % 4 := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]

/-- The words a step of the square root needs: with `y < 2^i` its root and
`r ≤ 2 y` its remainder before the step, `4 r + 3` and `4 y + 1` and the new root
are below `2^(64 L)` for `L = ⌊i / 64⌋ + 2`. -/
theorem pair_len {i y r : Nat} (hy : y < 2 ^ i) (hr : r ≤ 2 * y) :
    4 * r + 3 < 2 ^ (64 * (i / 64 + 2)) ∧ 4 * y + 1 < 2 ^ (64 * (i / 64 + 2)) ∧
      2 * y + 1 < 2 ^ (64 * (i / 64 + 2)) := by
  have h3 : 2 ^ (i + 3) ≤ 2 ^ (64 * (i / 64 + 2)) := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have : 2 ^ (i + 3) = 8 * 2 ^ i := by rw [Nat.pow_add]; omega_using []
  omega

end VG.Proof.Rsa.RecoverDet
