module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Bignum.SqrtRem
public import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Rsa.AArch64.RdStages
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

/-!
# `vg_rsa_recover_primes_det` on AArch64: the square root by words

As on RISC-V (`Proof/Rsa/RISCV64/RdSqrt.lean`), against `VG.Spec.Rsa.isqrt` through
`Proof/Bignum/SqrtRem.lean`: a digit's estimate and corrections (`DV`), and the first digit by bit
pairs (`first_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.Rsa (isqrt)

theorem wv_top (m : Mem) (B : Addr) (e n : Nat) :
    wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl

theorem wv_mod_low' (m : Mem) (B : Addr) (e a b : Nat) : wv m B e (a + b) % 2 ^ (64 * a) = wv m B e a :=
  wv_mod m B e (Nat.le_add_right a b)

/-- Two words, high and low. -/
abbrev v2 (h l : BitVec 64) : Nat := h.toNat * 2 ^ 64 + l.toNat

/-! ## A digit's estimate -/

open VG.Proof.Bignum.SqrtRem (IsDigit digit_lt digit_le_div)

/-- The estimate `q̂ = min(β - 1, ⌊⌊R / (2 β^m)⌋ / d₀⌋)` of a digit, from the root's top word
`d₀ ≥ β / 2` (`S = d₀ β^(m-1) + …`), is at least the digit and at most three above it. -/
theorem est_bounds {m S R P q d0 : Nat} (hm : 1 ≤ m) (hd0 : S / 2 ^ (64 * (m - 1)) = d0)
    (hd1 : 2 ^ 63 ≤ d0) (hR : R ≤ 2 * S) (hP : P < 2 ^ 64 * 2 ^ 64)
    (hq : IsDigit (2 ^ 64) S (R * (2 ^ 64 * 2 ^ 64) + P) q) :
    q ≤ min (2 ^ 64 - 1) ((R * (2 ^ 64 * 2 ^ 64) + P) / (2 * 2 ^ (64 * m)) / d0) ∧
      min (2 ^ 64 - 1) ((R * (2 ^ 64 * 2 ^ 64) + P) / (2 * 2 ^ (64 * m)) / d0) ≤ q + 3 := by
  obtain ⟨lo, hi⟩ := hq
  have hqβ : q < 2 ^ 64 := digit_lt hR hP lo
  have hM : 2 ^ (64 * m) = 2 ^ (64 * (m - 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hM]
  generalize hβ : (2 : Nat) ^ 64 = β at *
  generalize hRb : R * (β * β) + P = Rb at *
  generalize hA : 2 ^ (64 * (m - 1)) = A at *
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_two_pow
  have hβ2 : β = 2 * 2 ^ 63 := by rw [← hβ]; rfl
  -- `d₀ A ≤ S < (d₀ + 1) A`.
  have hS1 : d0 * A ≤ S := by rw [← hd0]; exact Nat.div_mul_le_self S A
  have hS2 : S < (d0 + 1) * A := by
    rw [← hd0, Nat.succ_mul]; exact Nat.lt_div_mul_add (by omega)
  have hS0 : 0 < S := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) hA1) hS1
  have hD : 0 < 2 * S * β := Nat.mul_pos (Nat.mul_pos (by decide) hS0) (by omega)
  have hE : 0 < 2 * (A * β) * d0 := Nat.mul_pos (Nat.mul_pos (by decide) (Nat.mul_pos hA1 (by omega))) (by omega)
  have hEle : 2 * (A * β) * d0 ≤ 2 * S * β := by
    have e : 2 * (A * β) * d0 = 2 * (d0 * A) * β := by ring
    rw [e]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hS1)
  refine ⟨?_, ?_⟩
  · refine Nat.le_min.mpr ⟨by omega, ?_⟩
    refine Nat.le_trans (digit_le_div hD lo) ?_
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left hEle hE
  · refine Nat.le_trans (Nat.min_le_right _ _) ?_
    rw [Nat.div_div_eq_div_mul]
    refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hE).mpr ?_)
    -- `Rb < 2 S β (q + 1) + (q + 1)² ≤ 2 (d₀ + 1) A β (q + 1) + β² ≤ 2 A β d₀ (q + 4)`.
    have h1 : Rb < 2 * S * β * (q + 1) + (q + 1) * (q + 1) := by
      have : (2 * S * β + (q + 1)) * (q + 1) = 2 * S * β * (q + 1) + (q + 1) * (q + 1) := by ring
      omega
    have h2 : (q + 1) * (q + 1) ≤ β * β := Nat.mul_le_mul (by omega) (by omega)
    have h3 : 2 * S * β * (q + 1) ≤ 2 * ((d0 + 1) * A) * β * (q + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    have h4 : β * β ≤ 2 * (A * β) * 2 ^ 63 := by
      have e : 2 * (A * β) * 2 ^ 63 = A * (β * β) := by rw [hβ2]; ring
      rw [e]; exact Nat.le_mul_of_pos_left _ hA1
    have e1 : (d0 + 1) * (q + 1) = d0 * q + d0 + q + 1 := by ring
    have e2 : d0 * (q + 4) = d0 * q + 4 * d0 := by ring
    have h5 : (d0 + 1) * (q + 1) + 2 ^ 63 ≤ d0 * (q + 4) := by rw [e1, e2]; omega
    have e3 : 2 * ((d0 + 1) * A) * β * (q + 1) + 2 * (A * β) * 2 ^ 63 =
        2 * (A * β) * ((d0 + 1) * (q + 1) + 2 ^ 63) := by ring
    calc Rb < 2 * S * β * (q + 1) + (q + 1) * (q + 1) := h1
      _ ≤ 2 * ((d0 + 1) * A) * β * (q + 1) + β * β := Nat.add_le_add h3 h2
      _ ≤ 2 * ((d0 + 1) * A) * β * (q + 1) + 2 * (A * β) * 2 ^ 63 := Nat.add_le_add_left h4 _
      _ = 2 * (A * β) * ((d0 + 1) * (q + 1) + 2 ^ 63) := e3
      _ ≤ 2 * (A * β) * (d0 * (q + 4)) := Nat.mul_le_mul_left _ h5
      _ = (q + 3).succ * (2 * (A * β) * d0) := by rw [Nat.succ_eq_add_one]; ring

/-! ## A digit and its corrections -/

open VG.Proof.Rsa.RecoverDet (isqrt_sq_le lt_succ_isqrt_sq)

theorem le_isqrt {t x : Nat} (h : t * t ≤ x) : t ≤ isqrt x := by
  refine Nat.le_of_not_lt fun c => ?_
  have := lt_succ_isqrt_sq x
  have : (isqrt x + 1) * (isqrt x + 1) ≤ t * t := Nat.mul_le_mul c c
  omega

/-- The digit after the root `S` of `A`: `isqrt (A β² + P) - S β`. -/
theorem digit_isqrt {β S R A P : Nat} (h : S * S + R = A) :
    IsDigit β S (R * (β * β) + P) (isqrt (A * (β * β) + P) - S * β) := by
  have lo := isqrt_sq_le (A * (β * β) + P)
  have hi := lt_succ_isqrt_sq (A * (β * β) + P)
  have hSb : S * β ≤ isqrt (A * (β * β) + P) := le_isqrt (by
    rw [← h]
    calc S * β * (S * β) = S * S * (β * β) := by ring
      _ ≤ (S * S + R) * (β * β) + P := Nat.le_add_right_of_le (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  obtain ⟨q, hq⟩ : ∃ q, isqrt (A * (β * β) + P) = S * β + q := ⟨_, (Nat.add_sub_of_le hSb).symm⟩
  rw [hq, Nat.add_sub_cancel_left]
  rw [hq] at lo hi
  have e1 : (S * β + q) * (S * β + q) = S * S * (β * β) + (2 * S * β + q) * q := by ring
  have e2 : (S * β + q + 1) * (S * β + q + 1) = S * S * (β * β) + (2 * S * β + (q + 1)) * (q + 1) := by ring
  have eA : A * (β * β) + P = S * S * (β * β) + (R * (β * β) + P) := by rw [← h]; ring
  rw [e1, eA] at lo
  rw [e2, eA] at hi
  exact ⟨by omega, by omega⟩

/-- `q (2 S β + q)`, what a digit `q` takes off the remainder. -/
abbrev qOf (D q : Nat) : Nat := q * (D + q)

theorem qOf_mono {D x y : Nat} (h : x ≤ y) : qOf D x ≤ qOf D y :=
  Nat.mul_le_mul h (Nat.add_le_add_left h _)

/-- The remainder `Rb - qOf D q̂` over `K` words as `V`, its sign `b`: `V + qOf D q̂ = Rb + b β^K`. -/
def Enc (E D Rb V qh b : Nat) : Prop := V + qOf D qh = Rb + b * E ∧ b ≤ 1

/-- The sign is whether the remainder is negative. -/
theorem Enc.sign {E D Rb V qh b : Nat} (h : Enc E D Rb V qh b) (hV : V < E) :
    b = if Rb < qOf D qh then 1 else 0 := by
  obtain ⟨e, hb⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · rw [Nat.zero_mul, Nat.add_zero] at e
    rw [ite_eq_right (by omega)]
  · rw [Nat.one_mul] at e
    rw [ite_eq_left (by omega)]

/-- A correction: where negative, `2 S β + 2 q̂ - 1` added back, the carry out `c`, and `q̂ - 1`. -/
theorem Enc.correct {E D Rb V V' qh b c : Nat} (h : Enc E D Rb V qh b) (hV : V < E)
    (hQ : qOf D qh < E) (hc : c ≤ 1) (hadd : V' + E * c = V + b * (D + 2 * qh - 1)) :
    Enc E D Rb V' (qh - b) (b * (1 - c)) := by
  obtain ⟨e, hb⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero] at e hadd ⊢
    have : c = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
      · exact h0
      · subst h1; omega
    subst this
    exact ⟨by omega, by omega⟩
  · simp only [Nat.one_mul] at e hadd ⊢
    have q1 : 1 ≤ qh := by
      rcases Nat.eq_zero_or_pos qh with h0 | h0
      · subst h0; simp only [qOf, Nat.zero_mul] at e; omega
      · exact h0
    have cs := VG.Proof.Bignum.SqrtRem.correction_step D qh q1
    have hQ' : qOf D qh = qOf D (qh - 1) + (D + 2 * qh - 1) := by simp only [qOf]; rw [Nat.mul_comm, cs, Nat.mul_comm]
    refine ⟨?_, by omega⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
    · subst h0; omega
    · subst h1; omega

/-- From an estimate at most three above the digit, three corrections give the digit. -/
theorem Enc.three {E D Rb V0 V1 V2 V3 q qh b0 c1 c2 c3 : Nat}
    (hq1 : qOf D q ≤ Rb) (hq2 : Rb < qOf D (q + 1)) (hlo : q ≤ qh) (hhi : qh ≤ q + 3)
    (h0 : Enc E D Rb V0 qh b0) (hV0 : V0 < E) (hV1 : V1 < E) (hV2 : V2 < E) (hV3 : V3 < E)
    (hQ : qOf D qh < E) (hc1 : c1 ≤ 1) (hc2 : c2 ≤ 1) (hc3 : c3 ≤ 1)
    (a1 : V1 + E * c1 = V0 + b0 * (D + 2 * qh - 1))
    (a2 : V2 + E * c2 = V1 + b0 * (1 - c1) * (D + 2 * (qh - b0) - 1))
    (a3 : V3 + E * c3 = V2 + b0 * (1 - c1) * (1 - c2) * (D + 2 * (qh - b0 - b0 * (1 - c1)) - 1)) :
    qh - b0 - b0 * (1 - c1) - b0 * (1 - c1) * (1 - c2) = q ∧ b0 * (1 - c1) * (1 - c2) * (1 - c3) = 0 ∧
      V3 = Rb - qOf D q := by
  have mono : ∀ x, q < x → Rb < qOf D x := fun x hx => Nat.lt_of_lt_of_le hq2 (qOf_mono hx)
  have mono' : ∀ x, x ≤ q → qOf D x ≤ Rb := fun x hx => Nat.le_trans (qOf_mono hx) hq1
  have hQle : ∀ x, x ≤ qh → qOf D x < E := fun x hx => Nat.lt_of_le_of_lt (qOf_mono hx) hQ
  have e1 := h0.correct hV0 hQ hc1 a1
  have e2 := e1.correct hV1 (hQle _ (Nat.sub_le _ _)) hc2 a2
  have e3 := e2.correct hV2 (hQle _ (by omega)) hc3 a3
  have s0 := h0.sign hV0
  have s1 := e1.sign hV1
  have s2 := e2.sign hV2
  have s3 := e3.sign hV3
  -- Each sign is whether the estimate is still above the digit.
  have sg : ∀ x b, b = (if Rb < qOf D x then 1 else 0) → q ≤ x → b = if q < x then 1 else 0 := by
    intro x b hb hx
    by_cases c : q < x
    · rw [hb, ite_eq_left (mono x c), ite_eq_left c]
    · rw [hb, ite_eq_right (by have := mono' x (by omega); omega), ite_eq_right c]
  have g0 := sg _ _ s0 hlo
  have g1 := sg _ _ s1 (by rw [g0]; split <;> omega)
  have g2 := sg _ _ s2 (by rw [g1, g0]; split <;> split <;> omega)
  have g3 := sg _ _ s3 (by rw [g2, g1, g0]; split <;> split <;> split <;> omega)
  have hx : qh - b0 - b0 * (1 - c1) - b0 * (1 - c1) * (1 - c2) = q := by
    rw [g2, g1, g0]; split <;> split <;> split <;> omega
  refine ⟨hx, ?_, ?_⟩
  · rw [g3, hx, ite_eq_right (Nat.lt_irrefl _)]
  · have := e3.1
    rw [hx, show b0 * (1 - c1) * (1 - c2) * (1 - c3) = 0 by rw [g3, hx, ite_eq_right (Nat.lt_irrefl _)],
      Nat.zero_mul, Nat.add_zero] at this
    omega

/-! ## The first digit -/

theorem isqrt_lt_pow {x i : Nat} (h : x < 4 ^ i) : isqrt x < 2 ^ i := by
  refine Nat.lt_of_not_le fun c => ?_
  have := isqrt_sq_le x
  have : 2 ^ i * 2 ^ i ≤ isqrt x * isqrt x := Nat.mul_le_mul c c
  have h' : x < 2 ^ i * 2 ^ i := by rwa [← Nat.mul_pow]
  omega

theorem isqrt_zero : isqrt 0 = 0 := by
  have := isqrt_sq_le 0
  refine Nat.eq_zero_of_not_pos fun c => ?_
  have : 1 * 1 ≤ isqrt 0 * isqrt 0 := Nat.mul_le_mul c c
  omega

/-- The arithmetic of a window's three pieces. -/
theorem combine3 {P Q x0 x0' W1 W1' xt xt' c1 c2 c E S2 : Nat} (A : x0' + P * c1 = x0 + E)
    (Bq : W1' + Q * c2 = W1 + S2 + c1) (C : xt' + P * c = xt + c2) :
    x0' + P * (W1' + Q * xt') + P * Q * P * c = x0 + P * (W1 + Q * xt) + (E + P * S2) := by
  have h1 : (x0' + P * (W1' + Q * xt') + P * Q * P * c) + (P * c1 + P * Q * c2) =
      (x0' + P * c1) + P * (W1' + Q * c2) + P * Q * (xt' + P * c) := by ring
  have h2 : (x0 + P * (W1 + Q * xt) + (E + P * S2)) + (P * c1 + P * Q * c2) =
      (x0 + E) + P * (W1 + S2 + c1) + P * Q * (xt + c2) := by ring
  rw [A, Bq, C] at h1
  omega

theorem msub3 {P Q q x0 x0' W1 W1' xt xt' c0 c1 b S2 : Nat} (A : x0' + q * q = x0 + P * c0)
    (Bq : W1' + q * S2 + c0 = W1 + Q * c1) (C : xt' + c1 = xt + P * b) :
    x0' + P * (W1' + Q * xt') + (q * q + P * (q * S2)) = x0 + P * (W1 + Q * xt) + P * Q * P * b := by
  have h1 : (x0' + P * (W1' + Q * xt') + (q * q + P * (q * S2))) + (P * c0 + P * Q * c1) =
      (x0' + q * q) + P * (W1' + q * S2 + c0) + P * Q * (xt' + c1) := by ring
  have h2 : (x0 + P * (W1 + Q * xt) + P * Q * P * b) + (P * c0 + P * Q * c1) =
      (x0 + P * c0) + P * (W1 + Q * c1) + P * Q * (xt + P * b) := by ring
  rw [A, Bq, C] at h1
  omega

/-- A number below `2^(64 m)` of `m + 1` words: its top word is zero. -/
theorem top_zero {mm : Mem} {B : Addr} {e m : Nat} (h : wv mm B e (m + 1) < 2 ^ (64 * m)) :
    word mm B (e + 8 * m) = 0 := by
  rw [wv_top] at h
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ (64 * m) * (word mm B (e + 8 * m)).toNat < 2 ^ (64 * m) * 1 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  show (word mm B (e + 8 * m)).toNat = 0
  omega

/-- A number at most `2^(64 m + 1)` of `m + 1` words: its top word is at most 1. -/
theorem top_le_one {mm : Mem} {B : Addr} {e m : Nat} (h : wv mm B e (m + 1) < 2 * 2 ^ (64 * m)) :
    (word mm B (e + 8 * m)).toNat ≤ 1 := by
  rw [wv_top] at h
  have : 2 ^ (64 * m) * (word mm B (e + 8 * m)).toNat < 2 ^ (64 * m) * 2 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-- What a digit takes off is below `β^(m+3)`. -/
theorem qOf_lt {Sv qh m : Nat} (hS : Sv < 2 ^ (64 * m)) (hq : qh ≤ 2 ^ 64 - 1) :
    qOf (2 * Sv * 2 ^ 64) qh < 2 ^ (64 * (m + 3)) := by
  have e : 2 ^ (64 * (m + 3)) = 2 ^ (64 * m) * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, show 64 * (m + 3) = 64 * m + 64 + 64 + 64 by omega]
  rw [e]
  generalize hA : 2 ^ (64 * m) = A at *
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_two_pow
  generalize hb : (2 : Nat) ^ 64 = β at *
  have hβ : 4 ≤ β := by rw [← hb]; decide
  -- `q̂ (2 S β + q̂) ≤ (β - 1) (2 (A - 1) β + β) < β · 2 A β ≤ A β β β`.
  have h1 : qh * (2 * Sv * β + qh) ≤ (β - 1) * (2 * Sv * β + (β - 1)) := Nat.mul_le_mul hq (by omega)
  have h2 : 2 * Sv * β + (β - 1) < 2 * A * β := by
    have : (Sv + 1) * β ≤ A * β := Nat.mul_le_mul_right _ hS
    have e1 : 2 * A * β = 2 * (A * β) := by ring
    have e2 : 2 * Sv * β = 2 * (Sv * β) := by ring
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have h3 : (β - 1) * (2 * Sv * β + (β - 1)) < β * (2 * A * β) :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) h2 (by omega)
  have h4 : β * (2 * A * β) ≤ A * β * β * β := by
    have e : β * (2 * A * β) = A * β * β * 2 := by ring
    rw [e]; exact Nat.mul_le_mul_left _ (by omega)
  unfold qOf
  omega

/-! ## The digits -/

/-- A number `S 2^(64 j)` of `j + n` words: its low `j` words are zero and the rest are `S`. -/
theorem wv_low_zero {mm : Mem} {B : Addr} {p j n S : Nat} (h : wv mm B p (j + n) = S * 2 ^ (64 * j)) :
    wv mm B p j = 0 ∧ wv mm B (p + 8 * j) n = S := by
  rw [wv_add] at h
  have hl := wv_lt mm B p j
  generalize wv mm B p j = L at *
  generalize wv mm B (p + 8 * j) n = H at *
  generalize 2 ^ (64 * j) = A at *
  have hA : 0 < A := by omega
  have e1 : (L + A * H) % A = L := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have e2 : (S * A) % A = 0 := Nat.mul_mod_left _ _
  rw [h] at e1
  have hL : L = 0 := by omega
  subst hL
  refine ⟨rfl, ?_⟩
  rw [Nat.zero_add] at h
  exact Nat.eq_of_mul_eq_mul_left hA (by rw [h, Nat.mul_comm])

/-- A number below `2^(64 a)` of `a + b` words: its low `a` words are it and the rest zero. -/
theorem wv_prefix {mm : Mem} {B : Addr} {p a b R : Nat} (h : wv mm B p (a + b) = R) (hR : R < 2 ^ (64 * a)) :
    wv mm B p a = R ∧ wv mm B (p + 8 * a) b = 0 := by
  rw [wv_add] at h
  have hl := wv_lt mm B p a
  generalize wv mm B p a = L at *
  generalize wv mm B (p + 8 * a) b = H at *
  generalize 2 ^ (64 * a) = A at *
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · subst h0; omega
  · have : A * 1 ≤ A * H := Nat.mul_le_mul_left _ h0; omega

/-- A word written where it was zero adds it at its place. -/
theorem wv_write_zero {mm : Mem} {B : Addr} {p i n : Nat} (y : BitVec 64) (h0 : word mm B (p + 8 * i) = 0)
    (hi : i < n) (fit : p + 8 * n ≤ 2 ^ 64) :
    wv (mm.writeW (off B (p + 8 * i)) y) B p n = wv mm B p n + 2 ^ (64 * i) * y.toNat := by
  obtain ⟨r, rfl⟩ : ∃ r, n = i + 1 + r := ⟨n - i - 1, by omega⟩
  have o := writeW_outside mm B (d := p + 8 * i) y (by omega)
  rw [wv_add _ _ _ (i + 1) r, wv_add _ _ _ (i + 1) r, wv_top, wv_top, h0,
    word_writeW_self, o.wv (by omega) (by omega), o.wv (by omega) (by omega)]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  ring

/-- After `m` digits (`W = 2 k`): the root `S` at `[wSN]`'s word `k - m` up (`d₀` its top word), the low
`W - 2 m` words of `[wR]` those of `Xn`, the remainder `R ≤ 2 S` in the `2 m` words above, and
`S² + R = ⌊Xn / β^(W - 2 m)⌋`. -/
def DV (mm : Mem) (B : Addr) (eR eS W k m Xn d0 : Nat) : Prop :=
  ∃ Sv R, wv mm B (eS) W = Sv * 2 ^ (64 * (k - m)) ∧ Sv / 2 ^ (64 * (m - 1)) = d0 ∧
    wv mm B (eR) (W - 2 * m) = Xn % 2 ^ (64 * (W - 2 * m)) ∧
    wv mm B (eR + 8 * (W - 2 * m)) (2 * m) = R ∧ R ≤ 2 * Sv ∧
    Sv * Sv + R = Xn / 2 ^ (64 * (W - 2 * m))

/-- A digit's step of `DV`: the window of `m + 3` words at word `W - 2 m - 2` of `[wR]` the new remainder,
and the digit at `[wSN]`'s word `k - m - 1`. -/
theorem dv_step {m0 mid : Mem} {B : Addr} {eR eS W k m Xn d0 : Nat} {y : BitVec 64}
    (hk : W = 2 * k) (hm1 : 1 ≤ m) (hmk : m < k) (hd0 : d0 < 2 ^ 64)
    (fitR : eR + 8 * (W + 2) ≤ 2 ^ 64) (fitS : eS + 8 * (W + 2) ≤ 2 ^ 64)
    (dRS : eR + 8 * (W + 2) ≤ eS ∨ eS + 8 * (W + 2) ≤ eR)
    (h : DV m0 B eR eS W k m Xn d0)
    (hout : Outside B (eR + (8 * W - 16 * m - 16)) (8 * (m + 3)) m0 mid)
    (hval : ∀ Sv R P q, wv m0 B (eS + 8 * (k - m)) (m + 1) = Sv →
      wv m0 B (eR + (8 * W - 16 * m - 16) + 16) (m + 1) = R →
      wv m0 B (eR + (8 * W - 16 * m - 16)) 2 = P → Sv / 2 ^ (64 * (m - 1)) = d0 → R ≤ 2 * Sv →
      IsDigit (2 ^ 64) Sv (R * (2 ^ 64 * 2 ^ 64) + P) q →
      wv mid B (eR + (8 * W - 16 * m - 16)) (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P - qOf (2 * Sv * 2 ^ 64) q ∧
        y.toNat = q) :
    DV (mid.writeW (off B (eS + 8 * (k - m) - 8)) y) B eR eS W k (m + 1) Xn d0 := by
  obtain ⟨Sv, R, hS, hd, hlow, hRv, hR2, hSR⟩ := h
  unfold DV
  generalize ho : W - 2 * m = o at *
  have ho2 : 2 ≤ o := by omega
  have hdo : eR + (8 * W - 16 * m - 16) = eR + 8 * (o - 2) := by omega
  rw [hdo] at hout hval
  rw [show eR + 8 * (o - 2) + 16 = eR + 8 * o by omega] at hval
  -- `S < β^m`.
  have hSl : Sv < 2 ^ (64 * m) := by
    have e : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by
      rw [← Nat.pow_add, show 64 * m = 64 + 64 * (m - 1) by omega]
    rw [e, ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hd]; exact hd0
  have hβm : 2 ^ (64 * m) * 2 ^ 64 = 2 ^ (64 * (m + 1)) := by
    rw [← Nat.pow_add, show 64 * m + 64 = 64 * (m + 1) by omega]
  -- The root's words.
  obtain ⟨low0, hhigh⟩ := wv_low_zero (j := k - m) (n := W - (k - m))
    (by rw [show k - m + (W - (k - m)) = W by omega]; exact hS)
  obtain ⟨Sv1, _⟩ := wv_prefix (a := m + 1) (b := W - (k - m) - (m + 1))
    (by rw [show m + 1 + (W - (k - m) - (m + 1)) = W - (k - m) by omega]; exact hhigh)
    (Nat.lt_of_lt_of_le hSl (Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * m ≤ 64 * (m + 1) by omega)))
  -- The remainder's words.
  have hRl : R < 2 ^ (64 * (m + 1)) := by
    rw [← hβm]
    have : 2 ^ (64 * m) * 2 ≤ 2 ^ (64 * m) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega
  obtain ⟨Rv1, Rhi0⟩ := wv_prefix (a := m + 1) (b := m - 1)
    (by rw [show m + 1 + (m - 1) = 2 * m by omega]; exact hRv) hRl
  -- The next pair and the low words.
  have hlow2 := hlow
  rw [show o = (o - 2) + 2 by omega, wv_add] at hlow2
  have hPl := wv_lt m0 B (eR + 8 * (o - 2)) 2
  have hLl := wv_lt m0 B eR (o - 2)
  have eo : 2 ^ (64 * (o - 2 + 2)) = 2 ^ (64 * (o - 2)) * (2 ^ 64 * 2 ^ 64) := by
    rw [← Nat.pow_add, ← Nat.pow_add, show 64 * (o - 2 + 2) = 64 * (o - 2) + (64 + 64) by omega]
  rw [eo] at hlow2
  generalize hP : wv m0 B (eR + 8 * (o - 2)) 2 = P at *
  generalize hL : wv m0 B eR (o - 2) = L at *
  have hP' : P = Xn / 2 ^ (64 * (o - 2)) % (2 ^ 64 * 2 ^ 64) := by
    rw [← Nat.mod_mul_right_div_self, ← hlow2, Nat.mul_comm (2 ^ (64 * (o - 2))) P,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hLl, Nat.zero_add]
  have hL' : L = Xn % 2 ^ (64 * (o - 2)) := by
    rw [← Nat.mod_mul_right_mod Xn (2 ^ (64 * (o - 2))) (2 ^ 64 * 2 ^ 64), ← hlow2,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLl]
  have hA : Xn / 2 ^ (64 * (o - 2)) = Xn / 2 ^ (64 * o) * (2 ^ 64 * 2 ^ 64) + P := by
    rw [hP']
    have h1 := Nat.div_add_mod (Xn / 2 ^ (64 * (o - 2))) (2 ^ 64 * 2 ^ 64)
    have h2 : Xn / 2 ^ (64 * (o - 2)) / (2 ^ 64 * 2 ^ 64) = Xn / 2 ^ (64 * o) := by
      rw [Nat.div_div_eq_div_mul, ← eo, show o - 2 + 2 = o by omega]
    rw [h2] at h1
    rw [Nat.mul_comm (Xn / 2 ^ (64 * o))]
    exact h1.symm
  -- The digit.
  have hq := digit_isqrt (β := 2 ^ 64) (P := P) hSR
  generalize hqd : isqrt (Xn / 2 ^ (64 * o) * (2 ^ 64 * 2 ^ 64) + P) - Sv * 2 ^ 64 = q at hq
  obtain ⟨hwin, hy⟩ := hval Sv R P q Sv1 Rv1 rfl hd hR2 hq
  obtain ⟨st1, st2⟩ := VG.Proof.Bignum.SqrtRem.step_inv (β := 2 ^ 64) (P := P) hSR hq
  have hqβ : q < 2 ^ 64 := digit_lt hR2 (show P < 2 ^ 64 * 2 ^ 64 from hPl) hq.1
  have qe : qOf (2 * Sv * 2 ^ 64) q = (2 * Sv * 2 ^ 64 + q) * q := Nat.mul_comm _ _
  rw [qe] at hwin
  -- The writes, outside the regions.
  have ow := writeW_outside mid B (d := eS + 8 * (k - m) - 8) y (by omega)
  refine ⟨Sv * 2 ^ 64 + q, R * (2 ^ 64 * 2 ^ 64) + P - (2 * Sv * 2 ^ 64 + q) * q, ?_, ?_, ?_, ?_, st2, ?_⟩
  · -- The root, with the digit below.
    have w0 : word mid B (eS + 8 * (k - m - 1)) = 0 := by
      rw [hout.word (by omega) (by omega)]
      have := (wv_eq_zero_iff _ _ _ _).mp low0 (k - m - 1) (by omega)
      exact this
    have hS' : wv mid B eS W = Sv * 2 ^ (64 * (k - m)) := by
      rw [hout.wv (by omega) (by omega), hS]
    rw [show eS + 8 * (k - m) - 8 = eS + 8 * (k - m - 1) by omega, wv_write_zero y w0 (by omega) (by omega), hS', hy,
      show k - (m + 1) = k - m - 1 by omega]
    have e : 2 ^ (64 * (k - m)) = 2 ^ (64 * (k - m - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * (k - m) = 64 * (k - m - 1) + 64 by omega]
    rw [e]; ring
  · -- The top word.
    rw [show m + 1 - 1 = m by omega]
    have e : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by
      rw [← Nat.pow_add, show 64 * m = 64 + 64 * (m - 1) by omega]
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm Sv, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hqβ,
      Nat.add_zero, hd]
  · -- The low words.
    rw [show W - 2 * (m + 1) = o - 2 by omega]
    rw [ow.wv (by omega) (by omega), hout.wv (by omega) (by omega), hL, hL']
  · -- The remainder: the window, then the words above it, zero.
    rw [show W - 2 * (m + 1) = o - 2 by omega, show 2 * (m + 1) = (m + 3) + (m - 1) by omega, wv_add,
      ow.wv (by omega) (by omega), ow.wv (by omega) (by omega), hwin,
      hout.wv (by omega) (by omega), show eR + 8 * (o - 2) + 8 * (m + 3) = eR + 8 * o + 8 * (m + 1) by omega,
      Rhi0, Nat.mul_zero, Nat.add_zero]
  · rw [show W - 2 * (m + 1) = o - 2 by omega, hA]
    exact st1

/-! ## Normalization -/

/-- The word at the top nonzero index `hi` of a number below `2^(64 (hi + 1))`: its quotient by `2^(64 hi)`. -/
theorem top_word_div {mm : Mem} {B : Addr} {p W hi : Nat} (hhi : hi < W)
    (hX : wv mm B p W < 2 ^ (64 * (hi + 1))) :
    (word mm B (p + 8 * hi)).toNat = wv mm B p W / 2 ^ (64 * hi) := by
  have e := wv_add mm B p (hi + 1) (W - (hi + 1))
  rw [show hi + 1 + (W - (hi + 1)) = W by omega, wv_top] at e
  have hl := wv_lt mm B p hi
  have hw := (word mm B (p + 8 * hi)).isLt
  have hz : wv mm B (p + 8 * (hi + 1)) (W - (hi + 1)) = 0 := by
    rcases Nat.eq_zero_or_pos (wv mm B (p + 8 * (hi + 1)) (W - (hi + 1))) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * (hi + 1)) * 1 ≤ 2 ^ (64 * (hi + 1)) * wv mm B (p + 8 * (hi + 1)) (W - (hi + 1)) :=
        Nat.mul_le_mul_left _ h0
      omega
  rw [hz, Nat.mul_zero, Nat.add_zero] at e
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl, Nat.zero_add]

/-- Normalized by the even part of its leading zeros, a number has its top two bits not both zero:
`X 2^c₂ ∈ [2^(64 W - 2), 2^(64 W))`, for `clz = 64 (W - 1 - hi) + z`, `T = ⌊X / 2^(64 hi)⌋` and
`2^63 ≤ T 2^z < 2^64`. -/
theorem norm_bounds {X T hi z W : Nat} (hT : T = X / 2 ^ (64 * hi))
    (hhi : hi < W) (hz : z ≤ 63) (h1 : 2 ^ 63 ≤ T * 2 ^ z) (h2 : T * 2 ^ z < 2 ^ 64) :
    2 ^ (64 * W - 2) ≤ X * 2 ^ ((64 * (W - 1 - hi) + z) / 2 * 2) ∧
      X * 2 ^ ((64 * (W - 1 - hi) + z) / 2 * 2) < 2 ^ (64 * W) := by
  generalize hc : 64 * (W - 1 - hi) + z = clz
  have hc2 : clz / 2 * 2 ≤ clz ∧ clz ≤ clz / 2 * 2 + 1 := by omega
  -- `X 2^clz = (T 2^z) 2^(64 (W - 1)) + (X mod 2^(64 hi)) 2^clz`.
  have hX' := Nat.div_add_mod X (2 ^ (64 * hi))
  rw [← hT] at hX'
  have hl := Nat.mod_lt X (Nat.two_pow_pos (64 * hi))
  generalize X % 2 ^ (64 * hi) = L at hX' hl
  have eA : 2 ^ (64 * hi) * 2 ^ clz = 2 ^ z * 2 ^ (64 * (W - 1)) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← hc]; congr 1; omega
  -- `(T + 1) 2^z ≤ 2^64`: `T 2^z` is a multiple of `2^z` below `2^64`.
  have hT1 : (T + 1) * 2 ^ z ≤ 2 ^ 64 := by
    have e : 2 ^ 64 = 2 ^ (64 - z) * 2 ^ z := by rw [← Nat.pow_add]; congr 1; omega
    rw [e] at h2 ⊢
    exact Nat.mul_le_mul_right _ (Nat.lt_of_mul_lt_mul_right h2)
  have lo : 2 ^ (64 * W - 1) ≤ X * 2 ^ clz := by
    have e : 2 ^ (64 * W - 1) = 2 ^ 63 * 2 ^ (64 * (W - 1)) := by rw [← Nat.pow_add]; congr 1; omega
    calc 2 ^ (64 * W - 1) = 2 ^ 63 * 2 ^ (64 * (W - 1)) := e
      _ ≤ T * 2 ^ z * 2 ^ (64 * (W - 1)) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (64 * hi) * T * 2 ^ clz := by
          rw [Nat.mul_comm (2 ^ (64 * hi)) T, Nat.mul_assoc T (2 ^ (64 * hi)), eA, Nat.mul_assoc]
      _ ≤ X * 2 ^ clz := Nat.mul_le_mul_right _ (by omega)
  have hi' : X * 2 ^ clz < 2 ^ (64 * W) := by
    have e : 2 ^ (64 * W) = 2 ^ 64 * 2 ^ (64 * (W - 1)) := by rw [← Nat.pow_add]; congr 1; omega
    calc X * 2 ^ clz < 2 ^ (64 * hi) * (T + 1) * 2 ^ clz :=
          Nat.mul_lt_mul_of_pos_right (by rw [Nat.mul_add, Nat.mul_one]; omega) (Nat.two_pow_pos _)
      _ = (T + 1) * 2 ^ z * 2 ^ (64 * (W - 1)) := by
          rw [Nat.mul_comm (2 ^ (64 * hi)), Nat.mul_assoc, eA, Nat.mul_assoc]
      _ ≤ 2 ^ 64 * 2 ^ (64 * (W - 1)) := Nat.mul_le_mul_right _ hT1
      _ = 2 ^ (64 * W) := e.symm
  refine ⟨?_, Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hc2.1)) hi'⟩
  -- `X 2^c₂ ≥ X 2^clz / 2`.
  rcases Nat.lt_or_ge (clz / 2 * 2) clz with c | c
  · have e : clz = clz / 2 * 2 + 1 := by omega
    rw [e, Nat.pow_succ, ← Nat.mul_assoc] at lo
    have e2 : 2 ^ (64 * W - 1) = 2 ^ (64 * W - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    rw [e2] at lo
    exact Nat.le_of_mul_le_mul_right lo (by decide)
  · rw [show clz / 2 * 2 = clz by omega]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) lo

/-! ## The square root -/

/-- The top two words of `W` words: `⌊X / β^(W - 2)⌋`. -/
theorem top2 (mm : Mem) (B : Addr) (p W : Nat) (hW : 2 ≤ W) :
    v2 (word mm B (p + 8 * W - 16 + 8)) (word mm B (p + 8 * W - 16)) = wv mm B p W / 2 ^ (64 * (W - 2)) := by
  have e := wv_add mm B p (W - 2) 2
  rw [show W - 2 + 2 = W by omega] at e
  have e2 : wv mm B (p + 8 * (W - 2)) 2 = v2 (word mm B (p + 8 * W - 16 + 8)) (word mm B (p + 8 * W - 16)) := by
    rw [show p + 8 * W - 16 = p + 8 * (W - 2) by omega, show p + 8 * (W - 2) + 8 = p + 8 * (W - 2) + 8 * 1 by omega]
    simp only [wv, v2, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.one_mul]
    omega
  rw [e, e2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add]

/-- After `first`: `DV` with one digit, its root `y` and remainder `r1:r0` over `[wR]`'s top two words, the root
into `[wSN]` (zero), from `[wR] = Xn`. -/
theorem dv_first {mm : Mem} {B : Addr} {eR eS W k Xn : Nat} {r1 r0 y : BitVec 64} (hk : W = 2 * k) (hk2 : 2 ≤ k)
    (fitR : eR + 8 * (W + 2) ≤ 2 ^ 64) (fitS : eS + 8 * (W + 2) ≤ 2 ^ 64)
    (dRS : eR + 8 * (W + 2) ≤ eS ∨ eS + 8 * (W + 2) ≤ eR)
    (hX : wv mm B (eR) W = Xn) (hS0 : wv mm B (eS) W = 0)
    (hy : y.toNat = isqrt (v2 (word mm B (eR + 8 * W - 16 + 8)) (word mm B (eR + 8 * W - 16))))
    (hr : v2 r1 r0 + y.toNat * y.toNat = v2 (word mm B (eR + 8 * W - 16 + 8)) (word mm B (eR + 8 * W - 16))) :
    DV (((mm.writeW (off B (eR + 8 * W - 16)) r0).writeW (off B (eR + 8 * W - 16 + 8)) r1).writeW
      (off B (eS + 8 * (W / 2) - 8)) y) B eR eS W k 1 Xn y.toNat := by
  rw [top2 mm B _ W (by omega), hX] at hy hr
  have hk' : W / 2 = k := by omega
  rw [hk']
  -- The writes, each outside the others' regions.
  have o0 := writeW_outside mm B (d := eR + 8 * W - 16) r0 (by omega)
  generalize m1e : mm.writeW (off B (eR + 8 * W - 16)) r0 = m1 at o0
  have o1 := writeW_outside m1 B (d := eR + 8 * W - 16 + 8) r1 (by omega)
  generalize m2e : m1.writeW (off B (eR + 8 * W - 16 + 8)) r1 = m2 at o1
  have o2 := writeW_outside m2 B (d := eS + 8 * k - 8) y (by omega)
  generalize m3e : m2.writeW (off B (eS + 8 * k - 8)) y = m3 at o2
  refine ⟨y.toNat, v2 r1 r0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `[wSN]`: zero but `y` at word `k - 1`.
    rw [← m3e, show eS + 8 * k - 8 = eS + 8 * (k - 1) by omega]
    have w0 : word m2 B (eS + 8 * (k - 1)) = 0 := by
      rw [o1.word (by omega) (by omega), o0.word (by omega) (by omega)]
      have := (wv_eq_zero_iff _ _ _ _).mp hS0 (k - 1) (by omega)
      exact this
    rw [wv_write_zero y w0 (by omega) (by omega), o1.wv (by omega) (by omega), o0.wv (by omega) (by omega),
      hS0, Nat.zero_add, Nat.mul_comm]
  · simp
  · -- The low words.
    rw [show W - 2 * 1 = W - 2 by omega, o2.wv (by omega) (by omega),
      o1.wv (by omega) (by omega), o0.wv (by omega) (by omega)]
    have := wv_mod_low' mm B (eR) (W - 2) 2
    rw [show W - 2 + 2 = W by omega, hX] at this
    exact this.symm
  · -- The remainder over the top two words.
    have wa : word m3 B (eR + 8 * W - 16 + 8) = r1 := by
      rw [o2.word (by omega) (by omega), ← m2e, word_writeW_self]
    have wb : word m3 B (eR + 8 * W - 16) = r0 := by
      rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega), ← m1e,
        word_writeW_self]
    rw [show W - 2 * 1 = W - 2 by omega, show 2 * 1 = 2 from rfl]
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one]
    rw [show eR + 8 * (W - 2) = eR + 8 * W - 16 by omega, wa, wb]
    simp only [v2]
    omega
  · -- `r ≤ 2 y`.
    have := lt_succ_isqrt_sq (Xn / 2 ^ (64 * (W - 2)))
    rw [← hy] at this
    have e : (y.toNat + 1) * (y.toNat + 1) = y.toNat * y.toNat + 2 * y.toNat + 1 := by ring
    omega
  · rw [show W - 2 * 1 = W - 2 by omega, Nat.add_comm]; exact hr

theorem sqrt_vals {Sv R X c : Nat} (h : Sv * Sv + R = X * 4 ^ c) (hR : R ≤ 2 * Sv) :
    Sv / 2 ^ c = isqrt X ∧ (R = 0 ↔ isqrt X * isqrt X = X) := by
  rw [Nat.mul_comm X] at h
  have e := VG.Proof.Bignum.SqrtRem.sqrt_of_rem h hR
  refine ⟨by rw [← e]; exact VG.Proof.Bignum.SqrtRem.norm_sqrt c X, ?_⟩
  rw [← VG.Proof.Bignum.SqrtRem.norm_square c X]
  exact (VG.Proof.Bignum.SqrtRem.square_iff_rem h hR).symm

/-- After every digit: the root in `[wSN]`, the remainder in `[wR]`. -/
theorem dv_last {mm : Mem} {B : Addr} {eR eS W k Xn d0 : Nat} (hk : W = 2 * k) (h : DV mm B eR eS W k k Xn d0) :
    ∃ Sv R, wv mm B (eS) W = Sv ∧ wv mm B (eR) W = R ∧ R ≤ 2 * Sv ∧
      Sv * Sv + R = Xn := by
  obtain ⟨Sv, R, h1, _, _, h4, h5, h6⟩ := h
  have z : W - 2 * k = 0 := by omega
  rw [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at h1
  rw [z, Nat.mul_zero, Nat.add_zero, ← hk] at h4
  rw [z, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h6
  exact ⟨Sv, R, h1, h4, h5, h6⟩

open VG.Proof.Rsa.RecoverDet (sqrtStep SqrtInv sqrtInv_step isqrt_sq_le lt_succ_isqrt_sq)
open VG.Spec.Rsa (isqrt)

/-! ## A bit pair of the first digit -/

abbrev sh2 (h l : BitVec 64) : BitVec 64 := h <<< 2 ||| l >>> 62

/-- The carry out of `a - b` with the carry in `c` (`subs`/`sbcs`): no borrow. -/
abbrev ncar (a b : BitVec 64) (c : Bool) : Bool := decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + c.toNat)

/-- `4 y + 1`, high and low word, from `x1 = y`. -/
abbrev tH (y : BitVec 64) : BitVec 64 := y <<< 1 >>> 63
abbrev tL (y : BitVec 64) : BitVec 64 := y <<< 1 <<< 1 ||| BitVec.setWidth 64 1#16

/-- `pairStep`'s carry: the remainder is at least `4 y + 1`. -/
abbrev pC (x2 x4 x5 y : BitVec 64) : Bool := ncar (sh2 x4 x5) (tH y) (ncar (sh2 x5 x2) (tL y) true)

abbrev pM (x2 x4 x5 y : BitVec 64) : BitVec 64 := 0 - (0 + 0 + BitVec.ofNat 64 (pC x2 x4 x5 y).toNat)

abbrev pR4 (x2 x4 x5 y : BitVec 64) : BitVec 64 :=
  sh2 x4 x5 ^^^ ((sh2 x4 x5 + ~~~(tH y) + BitVec.ofNat 64 (ncar (sh2 x5 x2) (tL y) true).toNat ^^^ sh2 x4 x5) &&&
    pM x2 x4 x5 y)

abbrev pR5 (x2 x4 x5 y : BitVec 64) : BitVec 64 :=
  sh2 x5 x2 ^^^ ((sh2 x5 x2 + ~~~(tL y) + BitVec.ofNat 64 true.toNat ^^^ sh2 x5 x2) &&& pM x2 x4 x5 y)

abbrev pY (x2 x4 x5 y : BitVec 64) : BitVec 64 := y <<< 1 ||| (0 + 0 + BitVec.ofNat 64 (pC x2 x4 x5 y).toNat)

theorem pairStep_ok (t : State) (h7 : t.gpr .x7 = 0) :
    WP isa (.block (pairStep ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      (t'.gpr .x2 = sh2 (t.gpr .x2) (t.gpr .x3) ∧ t'.gpr .x3 = t.gpr .x3 <<< 2 ∧
        t'.gpr .x4 = pR4 (t.gpr .x2) (t.gpr .x4) (t.gpr .x5) (t.gpr .x1) ∧
        t'.gpr .x5 = pR5 (t.gpr .x2) (t.gpr .x4) (t.gpr .x5) (t.gpr .x1) ∧
        t'.gpr .x1 = pY (t.gpr .x2) (t.gpr .x4) (t.gpr .x5) (t.gpr .x1) ∧
        t'.mem = t.mem ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x13, .x14, .x15, .x17] t t' :=
  WP.keep _ (by unfold pairStep; brun [h7]) (by decide) (by decide)
    (by decide +kernel)

theorem sq_and_shl_small (x c : BitVec 64) (k : Nat) (hc : c.toNat < 2 ^ k) : (x <<< k) &&& c = 0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
  by_cases h : i < k
  · simp [h]
  · have : c[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

theorem sh2_toNat (h l : BitVec 64) : (sh2 h l).toNat = 4 * h.toNat % 2 ^ 64 + l.toNat / 2 ^ 62 := by
  have hl := l.isLt
  have h1 : (h <<< 2).toNat = 4 * h.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h2 : (l >>> 62).toNat = l.toNat / 2 ^ 62 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small h (l >>> 62) 2 (by rw [h2]; omega)
  unfold sh2
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega

theorem v2_sh2 (a b c : BitVec 64) : v2 (sh2 a b) (sh2 b c) = (4 * v2 a b + c.toNat / 2 ^ 62) % 2 ^ 128 := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  simp only [v2, sh2_toNat]
  omega

/-- Two words less two words by `subs`, `sbcs`: the carry out is no borrow, and the difference. -/
theorem sub2c (xh xl yh yl : BitVec 64) :
    ncar xh yh (ncar xl yl true) = decide (v2 yh yl ≤ v2 xh xl) ∧
      (v2 yh yl ≤ v2 xh xl → v2 (xh + ~~~yh + BitVec.ofNat 64 (ncar xl yl true).toNat)
        (xl + ~~~yl + BitVec.ofNat 64 true.toNat) = v2 xh xl - v2 yh yl) := by
  have hxh := xh.isLt; have hxl := xl.isLt; have hyh := yh.isLt; have hyl := yl.isLt
  have nh : (~~~yh).toNat = 2 ^ 64 - 1 - yh.toNat := by rw [BitVec.toNat_not]
  have nl : (~~~yl).toNat = 2 ^ 64 - 1 - yl.toNat := by rw [BitVec.toNat_not]
  have cl : ncar xl yl true = decide (yl.toNat ≤ xl.toNat) := by
    simp only [ncar, nl, Bool.toNat_true]; exact decide_eq_decide.mpr (by omega)
  rw [cl]
  by_cases c : yl.toNat ≤ xl.toNat
  · simp only [c, decide_true, Bool.toNat_true, ncar, nh]
    refine ⟨decide_eq_decide.mpr (by simp only [v2]; omega), fun hle => ?_⟩
    simp only [v2, BitVec.toNat_add, BitVec.toNat_ofNat, nh, nl] at hle ⊢
    omega
  · simp only [c, decide_false, Bool.toNat_false, ncar, nh]
    refine ⟨decide_eq_decide.mpr (by simp only [v2]; omega), fun hle => ?_⟩
    simp only [v2, BitVec.toNat_add, BitVec.toNat_ofNat, nh, nl, Bool.toNat_true, Nat.zero_mod]
      at hle ⊢
    omega

theorem pM_mask (x2 x4 x5 y : BitVec 64) : pM x2 x4 x5 y = mask (pC x2 x4 x5 y) := by
  unfold pM; cases pC x2 x4 x5 y <;> rfl

theorem trial_v2 (y : BitVec 64) (hs : y.toNat < 2 ^ 63) : v2 (tH y) (tL y) = 4 * y.toNat + 1 := by
  have e1 : (y <<< 1).toNat = 2 * y.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e2 : (y <<< 1 >>> 63).toNat = 2 * y.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e1]
  have e3 : (y <<< 1 <<< 1).toNat = 4 * y.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, e1]; omega
  have hd := sq_and_shl_small (y <<< 1) (BitVec.setWidth 64 1#16) 1 (by decide)
  have e4 : (y <<< 1 <<< 1 ||| BitVec.setWidth 64 1#16).toNat = 4 * y.toNat % 2 ^ 64 + 1 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, e3]
    have : (BitVec.setWidth 64 1#16).toNat = 1 := rfl
    rw [this]; omega
  simp only [v2, tH, tL, e2, e4]
  omega

theorem pY_toNat (x2 x4 x5 y : BitVec 64) (hs : y.toNat < 2 ^ 63) :
    (pY x2 x4 x5 y).toNat = 2 * y.toNat + (pC x2 x4 x5 y).toNat := by
  have hb : (0 + 0 + BitVec.ofNat 64 (pC x2 x4 x5 y).toNat : BitVec 64).toNat < 2 ^ 1 := by
    cases pC x2 x4 x5 y <;> decide
  have hd := sq_and_shl_small y _ 1 hb
  unfold pY
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  cases pC x2 x4 x5 y <;> simp <;> omega

theorem x4_val (a2 a3 : BitVec 64) : v2 (sh2 a2 a3) (a3 <<< 2) = 4 * v2 a2 a3 % 2 ^ 128 := by
  have ha2 := a2.isLt; have ha3 := a3.isLt
  have e : (a3 <<< 2).toNat = 4 * a3.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  simp only [v2, sh2_toNat, e]
  omega

theorem pair_r (a2 a3 : BitVec 64) (R : Nat) :
    2 * (2 * R % 2 ^ 128 + 2 * v2 a2 a3 / 2 ^ 128) % 2 ^ 128 + 2 * (2 * v2 a2 a3 % 2 ^ 128) / 2 ^ 128 =
      (4 * R + a2.toNat / 2 ^ 62) % 2 ^ 128 := by
  have ha2 := a2.isLt; have ha3 := a3.isLt
  simp only [v2]; omega

theorem pair_x (X : Nat) : 2 * (2 * X % 2 ^ 128) % 2 ^ 128 = 4 * X % 2 ^ 128 := by omega

theorem pair_t {y : Nat} (hy : y < 2 ^ 63) : 2 * (2 * y) % 2 ^ 128 + 1 = 4 * y + 1 := by omega

theorem pair_y {y : Nat} (hy : y < 2 ^ 63) : 2 * y % 2 ^ 128 = 2 * y := by omega

/-- A step of `pairStep` is `sqrtStep 128 128` on the top two words `x2:x3`, the remainder `x4:x5` and the
root `y < 2^63`. -/
theorem pair_val (a2 a3 a4 a5 y : BitVec 64) (hs : y.toNat < 2 ^ 63) :
    sqrtStep 128 128 (v2 a2 a3, v2 a4 a5, y.toNat) =
      (v2 (sh2 a2 a3) (a3 <<< 2), v2 (pR4 a2 a4 a5 y) (pR5 a2 a4 a5 y), (pY a2 a4 a5 y).toNat) := by
  have tv := trial_v2 y hs
  obtain ⟨sb, sd⟩ := sub2c (sh2 a4 a5) (sh2 a5 a2) (tH y) (tL y)
  rw [tv] at sb sd
  have r4 : v2 (sh2 a4 a5) (sh2 a5 a2) = (4 * v2 a4 a5 + a2.toNat / 2 ^ 62) % 2 ^ 128 := v2_sh2 a4 a5 a2
  have hpc : pC a2 a4 a5 y = decide (4 * y.toNat + 1 ≤ v2 (sh2 a4 a5) (sh2 a5 a2)) := sb
  have m4 : pR4 a2 a4 a5 y = if pC a2 a4 a5 y then
      sh2 a4 a5 + ~~~(tH y) + BitVec.ofNat 64 (ncar (sh2 a5 a2) (tL y) true).toNat else sh2 a4 a5 := by
    unfold pR4; rw [pM_mask, sel_mask]
  have m5 : pR5 a2 a4 a5 y = if pC a2 a4 a5 y then
      sh2 a5 a2 + ~~~(tL y) + BitVec.ofNat 64 true.toNat else sh2 a5 a2 := by
    unfold pR5; rw [pM_mask, sel_mask]
  have ry := pY_toNat a2 a4 a5 y hs
  unfold sqrtStep
  simp only [pair_r, pair_y hs, pair_x, x4_val]
  rw [ry, m4, m5, ← r4, hpc, pair_t hs]
  by_cases c' : 4 * y.toNat + 1 ≤ v2 (sh2 a4 a5) (sh2 a5 a2)
  · have c : ¬ v2 (sh2 a4 a5) (sh2 a5 a2) < 4 * y.toNat + 1 := by omega
    simp only [c', c, decide_true, ↓reduceIte]
    rw [sd c', Bool.toNat_true]
  · have c : v2 (sh2 a4 a5) (sh2 a5 a2) < 4 * y.toNat + 1 := by omega
    simp only [c', c, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]

abbrev pairRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x13, .x14, .x15, .x17]

/-- `countLoop .x14 pairStep` from `T` in `x2:x3`, the root and remainder zero and `x14 = 64`: the root
`⌊√T⌋` in `x1` and the remainder `T - ⌊√T⌋²` in `x4:x5`. -/
theorem pairLoop_ok {s : State} (h1 : s.gpr .x1 = 0) (h4 : s.gpr .x4 = 0) (h5 : s.gpr .x5 = 0)
    (h7 : s.gpr .x7 = 0) (ht : s.gpr .x14 = BitVec.ofNat 64 64) :
    WP isa (countLoop .x14 pairStep) s fun t =>
      (t.gpr .x1).toNat = isqrt (v2 (s.gpr .x2) (s.gpr .x3)) ∧
        v2 (t.gpr .x4) (t.gpr .x5) + isqrt (v2 (s.gpr .x2) (s.gpr .x3)) * isqrt (v2 (s.gpr .x2) (s.gpr .x3)) =
          v2 (s.gpr .x2) (s.gpr .x3) ∧
        t.mem = s.mem ∧ Keep pairRegs s t := by
  have hT : v2 (s.gpr .x2) (s.gpr .x3) < 4 ^ 64 := by
    have := (s.gpr .x2).isLt; have := (s.gpr .x3).isLt; simp only [v2]; omega
  generalize hTe : v2 (s.gpr .x2) (s.gpr .x3) = T at hT ⊢
  let Inv : Nat → State → Prop := fun i t =>
    SqrtInv 64 T i (v2 (t.gpr .x2) (t.gpr .x3), v2 (t.gpr .x4) (t.gpr .x5), (t.gpr .x1).toNat) ∧
      t.mem = s.mem ∧ Keep pairRegs s t
  refine WP.mono (wp_countdown (body := .block (pairStep ++ ([.subImm .x .x14 .x14 1] : List Instr)))
    (cnt := .x14) (N := 64) (by decide) (by decide) Inv (fun i hi t ⟨jI, jm, jk⟩ _ => ?_) ?_ ht) ?_
  · refine WP.mono (pairStep_ok t ((jk.gpr .x7 (by decide)).trans h7))
      fun t' ⟨⟨u2, u3, u4, u5, u1, um, u14⟩, uk⟩ => ⟨⟨?_, by rw [um, jm], (jk.trans uk).mono (by decide)⟩, u14⟩
    have hy : (t.gpr .x1).toNat = isqrt (T / 4 ^ (64 - i)) := jI.2.1
    have hr : (t.gpr .x1).toNat < 2 ^ 63 := by
      rw [hy]
      refine Nat.lt_of_lt_of_le (isqrt_lt_pow (i := i) ?_) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add,
        show i + (64 - i) = 64 by omega]
      exact hT
    have e := pair_val (t.gpr .x2) (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x1) hr
    have st := sqrtInv_step (nb := 128) (K := 64) hi (by
      have := isqrt_lt_pow (i := 64) hT; omega) jI
    rw [e] at st
    rw [u2, u3, u4, u5, u1]
    exact st
  · refine ⟨?_, rfl, Keep.refl _ _⟩
    have z : T / 4 ^ 64 = 0 := Nat.div_eq_of_lt hT
    refine ⟨?_, ?_, ?_⟩
    · show v2 (s.gpr .x2) (s.gpr .x3) = T % 4 ^ (64 - 0) * 4 ^ 0
      rw [hTe, Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT]
    · show (s.gpr .x1).toNat = isqrt (T / 4 ^ (64 - 0))
      rw [Nat.sub_zero, z, isqrt_zero, h1]; rfl
    · show v2 (s.gpr .x4) (s.gpr .x5) + (s.gpr .x1).toNat * (s.gpr .x1).toNat = T / 4 ^ (64 - 0)
      rw [Nat.sub_zero, z, h1, h4, h5]; rfl
  · intro t ⟨jI, jm, jk⟩
    obtain ⟨_, hy, hr⟩ := jI
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hy hr
    rw [← hy]
    exact ⟨rfl, by rw [hy] at hr ⊢; exact hr, jm, jk⟩

/-- The reciprocal's loop, `countLoop .x13 divBit` from `x2 = 2^64 - 1 - d`, `x10 = 0`, `x13 = 64`, for `d` in
`x5`: the memory as it was, and where `d ≥ 2^63`, `x10 := ⌊(2^128 - 1) / d⌋ - 2^64`. -/
theorem recLoop_ok {s : State} {d : Nat} (hd : d < 2 ^ 64) (h5 : s.gpr .x5 = BitVec.ofNat 64 d)
    (h4 : s.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64) (h7 : s.gpr .x7 = 0)
    (h2 : s.gpr .x2 = BitVec.ofNat 64 (2 ^ 64 - 1 - d)) (h10 : s.gpr .x10 = BitVec.ofNat 64 0)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 64) :
    WP isa (countLoop .x13 R2Div.divBit) s fun t => t.mem = s.mem ∧ Keep [.x2, .x3, .x10, .x13, .x15, .x16] s t ∧
      (2 ^ 63 ≤ d → (t.gpr .x10).toNat = (2 ^ 128 - 1) / d - 2 ^ 64) := by
  by_cases hd' : 2 ^ 63 ≤ d
  · have hr0 : 2 ^ 64 - 1 - d < d := by omega
    have h0 : R2dRecInv s d (2 ^ 64 - 1 - d) 0 s :=
      ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - d, h2, h10, by simp, hr0⟩
    refine WP.mono (wp_countdown (N := 64) (by decide) (by decide) (R2dRecInv s d (2 ^ 64 - 1 - d))
      (fun k hk t hI _ => divStep_ok hd hr0 h4 h7 h5 hk hI) h0 h13) fun t hI => ⟨hI.mem, hI.keep, fun _ => ?_⟩
    obtain ⟨q, r, _, h10t, hP, hr⟩ := hI.val
    have hq : q = (2 ^ 128 - 1) / d - 2 ^ 64 := by
      rw [← WordStep.recip_eq hd (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
        Nat.add_zero]
    have hqB : q < 2 ^ 64 := by
      rw [hq]
      have : (2 ^ 128 - 1) / d < 2 ^ 65 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have := Nat.mul_le_mul_left (2 ^ 65) hd'
        omega
      omega
    rw [h10t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq]
  · refine WP.mono (wp_countdown (N := 64) (by decide) (by decide)
      (fun _ t => t.mem = s.mem ∧ Keep [.x2, .x3, .x10, .x13, .x15, .x16] s t)
      (fun k hk t ⟨hm, hk'⟩ _ => ?_) ⟨rfl, Keep.refl _ _⟩ h13) fun t ⟨hm, hk'⟩ => ⟨hm, hk', fun c => absurd c hd'⟩
    rw [WP.block_append_iff]
    refine WP.mono (r2dDivBit_ok t ((hk'.gpr .x4 (by decide)).trans h4) ((hk'.gpr .x7 (by decide)).trans h7))
      fun t₁ ⟨⟨_, _, m₁⟩, k₁⟩ => WP.mono (dec_ok t₁ .x13) fun t₂ ⟨⟨h13₂, m₂, _⟩, k₂⟩ =>
        ⟨⟨by rw [m₂, m₁, hm], (hk'.trans (k₁.trans k₂)).mono (by decide)⟩, by rw [h13₂, k₁.gpr .x13 (by decide)]⟩

/-- `DV` reads only the arrays' words. -/
theorem DV.congr {m m' : Mem} {B : Addr} {eR eS W k j Xn d0 : Nat} (h : DV m B eR eS W k j Xn d0)
    (hjW : 2 * j ≤ W)
    (hR : ∀ i < W, word m' B (eR + 8 * i) = word m B (eR + 8 * i))
    (hS : ∀ i < W, word m' B (eS + 8 * i) = word m B (eS + 8 * i)) : DV m' B eR eS W k j Xn d0 := by
  obtain ⟨Sv, R, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Sv, R, ?_, h2, ?_, ?_, h5, h6⟩
  · rw [wv_congr fun i hi => hS i hi]; exact h1
  · rw [wv_congr fun i hi => hR i (by omega)]; exact h3
  · refine (wv_congr fun i hi => ?_).trans h4
    have := hR (W - 2 * j + i) (by omega)
    rwa [show eR + 8 * (W - 2 * j + i) = eR + 8 * (W - 2 * j) + 8 * i by omega] at this

/-- `first`'s head: the bases, `T` (the top two words of `[wX4]`) into `x2:x3`, the root and remainder zero. -/
theorem fHead_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block (sqBases ++ ([.lsl .x .x3 .x12 3, .add .x .x16 .x10 .x3, .subImm .x .x16 .x16 16, ld .x2 .x16 8,
      ld .x3 .x16, movi .x1 0, movi .x4 0, movi .x5 0, movi .x14 64] : List Instr))) s fun t =>
      G I m₀ (Wk I.k) c t ∧ Frm I.B hdrW s.mem t.mem ∧
      t.gpr .x10 = off I.B (slot (Wk I.k) wX4) ∧ t.gpr .x11 = off I.B (slot (Wk I.k) wS) ∧
      t.gpr .x12 = BitVec.ofNat 64 (Wk I.k) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x16 = off I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16) ∧
      t.gpr .x2 = word t.mem I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16 + 8) ∧
      t.gpr .x3 = word t.mem I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16) ∧
      t.gpr .x1 = 0 ∧ t.gpr .x4 = 0 ∧ t.gpr .x5 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 64 ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x7, .x9, .x10, .x11, .x12, .x14, .x16] s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  simp only [sqBases, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  have hn := g₁.ws.scr.nowrap
  have hZ := g₁.ws.hZ
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  rw [WP.block_append_iff]
  refine WP.mono (ws_ok g₁.ws.scr g₁.ws.x0 g₁.ws.h256 g₁.ws.hw g₁.ws.hS) fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ => ?_
  have x0₂ : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans g₁.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wX4 .x10 x0₂ h11) fun s₃ ⟨⟨h10, m₃, _⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wS .x9 ((k₃.gpr .x0 (by decide)).trans x0₂) ((k₃.gpr .x11 (by decide)).trans h11))
    fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_
  have hs₄ := g₁.ws.scr.congr ((k₂.trans k₃).trans k₄).wr
  have h10₄ : s₄.gpr .x10 = off I.B (slot (Wk I.k) wX4) := (k₄.gpr .x10 (by decide)).trans h10
  have h12₄ : s₄.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by rw [k₄.gpr .x12 (by decide), k₃.gpr .x12 (by decide), h12]
  have e16 : off I.B (slot (Wk I.k) wX4) + BitVec.ofNat 64 (Wk I.k) <<< 3 - BitVec.ofNat 64 16 =
      off I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16) := by
    rw [shl_ofNat (show Wk I.k * 2 ^ 3 < 2 ^ 64 by omega), off_add, off_sub I.B (by omega)]
    congr 2; omega
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x7, .x11, .x14, .x16] (Q := fun t =>
      t.gpr .x11 = off I.B (slot (Wk I.k) wS) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x16 = off I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16) ∧
      t.gpr .x2 = word s₄.mem I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16 + 8) ∧
      t.gpr .x3 = word s₄.mem I.B (slot (Wk I.k) wX4 + 8 * Wk I.k - 16) ∧
      t.gpr .x1 = 0 ∧ t.gpr .x4 = 0 ∧ t.gpr .x5 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 64 ∧ t.mem = s₄.mem) (by
    brun [h9, h10₄, h12₄, e16, off_add, hs₄.ld (show slot (Wk I.k) wX4 + 8 * Wk I.k - 16 + 8 + 8 ≤ I.Z by omega),
      hs₄.ld (show slot (Wk I.k) wX4 + 8 * Wk I.k - 16 + 8 ≤ I.Z by omega)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨t11, t7, t16, t2, t3, t1, t4, t5, t14, mt⟩, kt⟩ => ?_
  have m4 : t.mem = s₁.mem := by rw [mt, m₄, m₃, m₂]
  refine ⟨g₁.same m4 (((k₂.trans k₃).trans k₄).trans kt) (by decide), by rw [m4]; exact f₁,
    by rw [kt.gpr .x10 (by decide)]; exact h10₄, t11, by rw [kt.gpr .x12 (by decide)]; exact h12₄, t7, t16,
    by rw [t2, mt], by rw [t3, mt], t1, t4, t5, t14, ((((k₁.trans k₂).trans k₃).trans k₄).trans kt).mono (by decide)⟩

/-- `first`'s middle: the remainder over `T`, the root into `sS0` and the root's word `W / 2 - 1`, and the
reciprocal's start. -/
theorem fMid_ok {s : State} {B : Addr} {Z eT eS W : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h16 : s.gpr .x16 = off B eT) (h12 : s.gpr .x12 = BitVec.ofNat 64 W) (h11 : s.gpr .x11 = off B eS)
    (h7 : s.gpr .x7 = 0) (hW : 2 ≤ W) (hW' : W < 2 ^ 24) (hT : eT + 16 ≤ Z) (hS : eS + 8 * W ≤ Z)
    (hH : 8 * 32 ≤ Z) :
    WP isa (.block [st .x5 .x16, st .x4 .x16 8, sth .x1 sS0, .lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3,
      .add .x .x3 .x11 .x3, .subImm .x .x3 .x3 8, st .x1 .x3, mov .x5 .x1, .sub .x .x2 .x7 .x5, .subImm .x .x2 .x2 1,
      movi .x10 0, movi .x4 1, movi .x13 64]) s fun t =>
      (t.mem = (((s.mem.writeW (off B eT) (s.gpr .x5)).writeW (off B (eT + 8)) (s.gpr .x4)).writeW (off B (8 * sS0))
          (s.gpr .x1)).writeW (off B (eS + 8 * (W / 2) - 8)) (s.gpr .x1) ∧
        t.gpr .x5 = s.gpr .x1 ∧ t.gpr .x2 = 0 - s.gpr .x1 - BitVec.ofNat 64 1 ∧ t.gpr .x10 = BitVec.ofNat 64 0 ∧
        t.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64 ∧ t.gpr .x13 = BitVec.ofNat 64 64) ∧
      Keep [.x2, .x3, .x4, .x5, .x10, .x13] s t := by
  have hn := hs.nowrap
  have e3 : off B eS + (BitVec.ofNat 64 W >>> 1) <<< 3 - BitVec.ofNat 64 8 = off B (eS + 8 * (W / 2) - 8) := by
    have : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
    rw [this, shl_ofNat (show W / 2 * 2 ^ 3 < 2 ^ 64 by omega), off_add, off_sub B (by omega)]
    congr 2; omega
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, h16, h12, h11, h7, e3, off_add, hdr_enc (show sS0 < 32 by decide), hs.st (show eT + 8 ≤ Z by omega),
    hs.st (show eT + 8 + 8 ≤ Z by omega), hs.st (show 8 * sS0 + 8 ≤ Z by simp only [sS0, sFn]; omega),
    hs.st (show eS + 8 * (W / 2) - 8 + 8 ≤ Z by omega)]

/-- A header word written before a word of the arrays leaves the arrays' words as without it. -/
theorem word_swap_hdr {m : Mem} {B : Addr} {h a b : Nat} {u v : BitVec 64} (hh : h + 8 ≤ 256) (ha : 256 ≤ a)
    (hb : 256 ≤ b) (hab : a + 8 ≤ b ∨ b + 8 ≤ a ∨ a = b) (ha' : a + 8 ≤ 2 ^ 64) (hb' : b + 8 ≤ 2 ^ 64) :
    word ((m.writeW (off B h) u).writeW (off B b) v) B a = word (m.writeW (off B b) v) B a := by
  rcases hab with hab | hab | rfl
  · rw [(writeW_outside _ B _ hb').word (.inl hab) ha', (writeW_outside _ B _ hb').word (.inl hab) ha',
      (writeW_outside _ B _ (by omega)).word (.inr (by omega)) ha']
  · rw [(writeW_outside _ B _ hb').word (.inr hab) ha', (writeW_outside _ B _ hb').word (.inr hab) ha',
      (writeW_outside _ B _ (by omega)).word (.inr (by omega)) ha']
  · rw [word_writeW_self, word_writeW_self]

/-- `first`: of the top two words `T` of `X` (wide array `wX4`), the root `y = ⌊√T⌋` into `sS0` and the root's
word `W / 2 - 1` (wide array `wS`, zero), the remainder `T - y²` over `T` (`DV` after one digit), and `y`'s
reciprocal (where `y ≥ 2^63`) into `sV`. -/
theorem first_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    (hS0 : wv s.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0) :
    WP isa first s fun t => G I m₀ (Wk I.k) c t ∧
      Frm I.B (hdrW ++ [(8 * sS0, 8), (8 * sV, 8), (slot (Wk I.k) wX4 + 8 * Wk I.k - 16, 16),
        (slot (Wk I.k) wS + 8 * (Wk I.k / 2) - 8, 8)]) s.mem t.mem ∧
      (word t.mem I.B (8 * sS0)).toNat = isqrt (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) / 2 ^ (64 * (Wk I.k - 2))) ∧
      (2 ^ 63 ≤ (word t.mem I.B (8 * sS0)).toNat →
        (word t.mem I.B (8 * sV)).toNat = (2 ^ 128 - 1) / (word t.mem I.B (8 * sS0)).toNat - 2 ^ 64) ∧
      DV t.mem I.B (slot (Wk I.k) wX4) (slot (Wk I.k) wS) (Wk I.k) (Wk I.k / 2) 1
        (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k)) (word t.mem I.B (8 * sS0)).toNat := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega
  have hv1 : 1 ≤ vk I.k := by simp only [vk]; omega
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  have cS0 : 8 * sS0 = 240 := rfl
  have cV : 8 * sV = 200 := rfl
  unfold first
  simp only [seqs]
  refine WP.seq (WP.mono (fHead_ok h L) fun s₁ ⟨g₁, f₁, h10, h11, h12, h7, h16, h2, h3, h1, h4, h5, h14, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZ := g₁.ws.hZ
  refine WP.seq (WP.mono (pairLoop_ok h1 h4 h5 h7 h14) fun s₂ ⟨y2, r2, m2, k2⟩ => ?_)
  rw [h2, h3] at y2 r2
  have g₂ : G I m₀ (Wk I.k) c s₂ := g₁.same m2 k2 (by decide)
  have k12 := k2
  refine WP.seq (WP.mono (fMid_ok (eT := slot (Wk I.k) wX4 + 8 * Wk I.k - 16) (eS := slot (Wk I.k) wS)
    (W := Wk I.k) g₂.ws.scr g₂.ws.x0 (by rw [k2.gpr .x16 (by decide)]; exact h16)
    (by rw [k2.gpr .x12 (by decide)]; exact h12) (by rw [k2.gpr .x11 (by decide)]; exact h11)
    (by rw [k2.gpr .x7 (by decide)]; exact h7) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨m3, h5₃, h2₃, h10₃, h4₃, h13₃⟩, k₃⟩ => ?_)
  generalize hy : s₂.gpr .x1 = y at m3 h5₃ h2₃ y2
  have yl := y.isLt
  have e2 : (0 : BitVec 64) - y - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ 64 - 1 - y.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
    omega
  refine WP.seq (WP.mono (recLoop_ok (d := y.toNat) yl (by rw [h5₃, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h4₃
    (by rw [k₃.gpr .x7 (by decide), k2.gpr .x7 (by decide)]; exact h7) (by rw [h2₃, e2]) h10₃ h13₃)
    fun s₄ ⟨m4, k4, v4⟩ => ?_)
  -- The stores' frame.
  have F3 : Frm I.B ([(slot (Wk I.k) wX4 + 8 * Wk I.k - 16, 16), (slot (Wk I.k) wS + 8 * (Wk I.k / 2) - 8, 8)] ++
      [(8 * sS0, 8)]) s₂.mem s₃.mem := by
    rw [m3]
    refine (((Frm.of_outside (Outside.mono (o' := slot (Wk I.k) wX4 + 8 * Wk I.k - 16) (n' := 16)
        (writeW_outside _ I.B _ (by omega)) (by omega) (by omega)) ?_).trans
      (Frm.of_outside (Outside.mono (o' := slot (Wk I.k) wX4 + 8 * Wk I.k - 16) (n' := 16)
        (writeW_outside _ I.B _ (by omega)) (by omega) (by omega)) ?_)).trans
      (Frm.of_outside (writeW_outside _ I.B _ (by omega)) ?_)).trans
      (Frm.of_outside (writeW_outside _ I.B _ (by omega)) ?_)
    all_goals simp
  have g₃ : G I m₀ (Wk I.k) c s₃ := g₂.frmOwn (sl := sS0) ⟨by decide, by decide, by decide⟩ F3
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> dsimp only <;> omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> dsimp only <;> omega)
    k₃ (by decide)
  have g₄ : G I m₀ (Wk I.k) c s₄ := g₃.same m4 k4 (by decide)
  refine WP.mono (sthOwn_ok g₄ (sl := sV) ⟨by decide, by decide, by decide⟩ .x10) fun t ⟨gt, ft, wt, kt⟩ => ?_
  -- The words of the arrays and of `sS0`.
  have wS0 : word t.mem I.B (8 * sS0) = y := by
    rw [ft.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega) (by omega), m4, m3,
      (writeW_outside _ I.B _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have mT : ∀ a, 256 ≤ a → a + 8 ≤ I.Z → word t.mem I.B a = word s₃.mem I.B a := fun a ha ha' => by
    rw [ft.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega) (by omega), m4]
  have m1 : s₂.mem = s₁.mem := m2
  have hX1 : wv s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) :=
    Frm.hdrW_wv f₁ (by omega) (by omega)
  have hS1 : wv s₁.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0 := by rw [Frm.hdrW_wv f₁ (by omega) (by omega), hS0]
  have yv : y.toNat = isqrt (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) / 2 ^ (64 * (Wk I.k - 2))) := by
    rw [y2, top2 _ _ _ _ (by omega), hX1]
  rw [wS0]
  refine ⟨gt, ?_, yv, fun hy63 => ?_, ?_⟩
  · refine (f₁.mono fun r hr => List.mem_append_left _ hr).trans ((by rw [← m2]; exact Frm.refl _ _ _ :
      Frm I.B _ s₁.mem s₂.mem).trans ((F3.mono fun r hr => ?_).trans ((by rw [m4]; exact Frm.refl _ _ _ :
      Frm I.B _ s₃.mem s₄.mem).trans (ft.mono fun r hr => ?_))))
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (rfl | rfl) | rfl <;> simp
    · simp only [List.mem_singleton] at hr; subst hr; simp
  · rw [wt, v4 hy63]
  · have dv := dv_first (mm := s₁.mem) (eR := slot (Wk I.k) wX4) (eS := slot (Wk I.k) wS) (W := Wk I.k)
      (k := Wk I.k / 2) (r1 := s₂.gpr .x4) (r0 := s₂.gpr .x5) (y := y) (by omega) (by omega) (by omega) (by omega)
      (by omega) hX1 hS1 y2 (by rw [y2]; exact r2)
    refine dv.congr (by omega) (fun i hi => ?_) (fun i hi => ?_)
    · rw [mT _ (by omega) (by omega), m3, m2, word_swap_hdr (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
    · rw [mT _ (by omega) (by omega), m3, m2, word_swap_hdr (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]

end VG.Proof.Rsa.AArch64.Rd
