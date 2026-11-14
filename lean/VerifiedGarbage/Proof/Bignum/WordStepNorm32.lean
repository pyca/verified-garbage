module
-- separate module: target-independent, for every 32-bit target's word steps of `R² mod n` (x86's now)
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.WordStep32

/-!
# Multiword arithmetic: a 3-by-2 step of long division by 32-bit words

`WordStepNorm`'s 3-by-2 estimate and one add-back for 32-bit words
(`Impl/Bignum/X86/R2Words.lean`), as `WordStep32` is `WordStep`'s:

* `qhat_trunc`: an estimate from the top three words of the dividend and the
  top two of the divisor (above the same power of two) is `q ≤ q̂ ≤ q + 1`,
  and `wordStepQ1_val`: then `m` added once if negative is `x 2^32 mod m`;
* `qhat3_norm`, `quot3_val`: that estimate from the 2-by-1 estimate,
  corrected by `U - q̂ D` over three words (Knuth's step D3);
* `qhat3_div`, `wordStepQ1_div`: the same for any dividend `y < 2^32 m`, as
  a step that brings down a word of the dividend has (`WordStepNorm`'s).
-/

@[expose] public section

namespace VG.Proof.Bignum.WordStep32

theorem lt_succ_div_mul (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  omega_using [h1, h2]

/-- An estimate of `⌊Y / N⌋ < 2^32` from `Y` and `N` cut at `2^K`, whose top
`⌊N / 2^K⌋` is at least `2^32`: `q ≤ min(⌊⌊Y / 2^K⌋ / ⌊N / 2^K⌋⌋, 2^32 - 1) ≤ q + 1`. -/
theorem qhat_trunc {Y N K : Nat} (hq : Y / N < 2 ^ 32) (hD : 2 ^ 32 ≤ N / 2 ^ K) :
    Y / N ≤ min (Y / 2 ^ K / (N / 2 ^ K)) (2 ^ 32 - 1) ∧
      min (Y / 2 ^ K / (N / 2 ^ K)) (2 ^ 32 - 1) ≤ Y / N + 1 := by
  have hK := Nat.two_pow_pos K
  have hD0 : 0 < N / 2 ^ K := by omega_using [hD]
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hD0
  generalize hq' : Y / N = q at hq
  generalize hU : Y / 2 ^ K = U
  generalize hDd : N / 2 ^ K = D at hD hD0
  have hNd : D * 2 ^ K ≤ N := by rw [← hDd]; exact Nat.div_mul_le_self N _
  have hN1 : N < (D + 1) * 2 ^ K := by rw [← hDd]; exact lt_succ_div_mul _ _ hK
  have hUY : U * 2 ^ K ≤ Y := by rw [← hU]; exact Nat.div_mul_le_self Y _
  have hY1 : Y < (U + 1) * 2 ^ K := by rw [← hU]; exact lt_succ_div_mul _ _ (by omega_using [hK])
  have hqN : q * N ≤ Y := by rw [← hq']; exact Nat.div_mul_le_self Y N
  have hYq : Y < (q + 1) * N := by rw [← hq']; exact lt_succ_div_mul _ _ (by omega_using [hN0])
  constructor
  · refine Nat.le_min.mpr ⟨?_, by omega_using [hq]⟩
    rw [Nat.le_div_iff_mul_le hD0]
    -- `q D 2^K ≤ q N ≤ Y`, so `q D ≤ U`.
    have h1 : q * D * 2 ^ K ≤ Y := by
      rw [Nat.mul_assoc]; exact Nat.le_trans (Nat.mul_le_mul_left q hNd) hqN
    have h2 : q * D < U + 1 := by
      have := Nat.lt_of_le_of_lt h1 hY1
      exact Nat.lt_of_mul_lt_mul_right this
    omega_using [hq', hq, hU, hDd, hD, hD0, hNd, hN1, hUY, hY1, hqN, hYq, h1, h2]
  · refine Nat.le_trans (Nat.min_le_left _ _) ?_
    -- `q̂ D ≤ U`, `U 2^K ≤ Y < (q + 1) N < (q + 1) (D + 1) 2^K`.
    refine Nat.le_of_not_lt fun hc => ?_
    have hge : q + 2 ≤ U / D := by omega_using [hq', hq, hU, hDd, hD, hD0, hNd, hN1, hUY, hY1, hqN, hYq, hc]
    have h1 : (q + 2) * D ≤ U := Nat.le_trans (Nat.mul_le_mul_right D hge) (Nat.div_mul_le_self U D)
    have h2 : U < (q + 1) * (D + 1) := by
      have h3 : U * 2 ^ K < (q + 1) * (D + 1) * 2 ^ K := by
        rw [Nat.mul_assoc]
        exact Nat.lt_of_le_of_lt hUY (Nat.lt_of_lt_of_le hYq (Nat.mul_le_mul_left _ (Nat.le_of_lt hN1)))
      exact Nat.lt_of_mul_lt_mul_right h3
    have e1 : (q + 2) * D = (q + 1) * D + D := by rw [Nat.add_mul, Nat.add_mul (q) 1, Nat.one_mul]; omega_using []
    have e2 : (q + 1) * (D + 1) = (q + 1) * D + (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
    omega_using [hK, hN0, hq', hq, hU, hDd, hD, hD0, hNd, hN1, hUY, hY1, hqN, hYq, hc, hge, h1, h2, e1, e2]

/-- `y - q̂ m` with `m` added once if it is negative is `y mod m`, for
`⌊y / m⌋ ≤ q̂ ≤ ⌊y / m⌋ + 1`. -/
theorem addBack_one {W y m qh : Nat} (hm : 0 < m) (hW : 2 * m < W / 2)
    (h1 : y / m ≤ qh) (h2 : qh ≤ y / m + 1) :
    addIfNeg m ((y : Int) - (qh * m : Nat)) = ((y % m : Nat) : Int) ∧
      -((W : Int) / 2) ≤ (y : Int) - (qh * m : Nat) ∧ (y : Int) - (qh * m : Nat) < (W : Int) / 2 := by
  have hy := Nat.div_add_mod y m
  have hr := Nat.mod_lt y hm
  obtain ⟨c, hc, hqm⟩ : ∃ c, c ≤ 1 ∧ qh * m = y / m * m + c * m :=
    ⟨qh - y / m, by omega_using [h2], by rw [← Nat.add_mul]; congr 1; omega_using [h1]⟩
  have hyP : y = y / m * m + y % m := by rw [Nat.mul_comm]; omega_using [hy]
  rw [hqm]
  generalize y / m * m = P at *
  generalize y % m = r at *
  subst hyP
  unfold addIfNeg
  rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> push_cast <;>
    (repeat' split) <;> omega_arith

/-- A step of long division over the words of a dividend `y < 2^32 m`, for
any estimate `q ≤ q̂ ≤ q + 1` of `q = ⌊y / m⌋`: `t₁ = y - q̂ m` modulo
`W > 4 m` (with its borrow `b`) and `m` added once to it if its top half is
set (with the carry `c`) is `y mod m`. -/
theorem wordStepQ1_div {W Y M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : Y / M ≤ qh) (hle : qh ≤ Y / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = Y + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = Y % M := by
  obtain ⟨hfin, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hw1 : -((W : Int) / 2) ≤ addIfNeg M ((Y : Nat) - (qh * M : Nat)) := by
    rw [hfin]; omega_using []
  have hw2 : addIfNeg M ((Y : Nat) - (qh * M : Nat)) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt Y hM0; omega_using [hMW, this]
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, hfin]
  have hr := Nat.mod_lt Y hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- A step of long division over the words, for any estimate `q ≤ q̂ ≤ q + 1`
of `q = ⌊x 2^32 / m⌋`: `t₁ = x 2^32 - q̂ m` modulo `W > 4 m` (with its borrow
`b`) and `m` added once to it if its top half is set (with the carry `c`) is
`x 2^32 mod m`. -/
theorem wordStepQ1_val {W X M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : X * 2 ^ 32 / M ≤ qh) (hle : qh ≤ X * 2 ^ 32 / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = X * 2 ^ 32 + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = X * 2 ^ 32 % M := by
  obtain ⟨hfin, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hw1 : -((W : Int) / 2) ≤ addIfNeg M ((X * 2 ^ 32 : Nat) - (qh * M : Nat)) := by
    rw [hfin]; omega_using []
  have hw2 : addIfNeg M ((X * 2 ^ 32 : Nat) - (qh * M : Nat)) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 32) hM0; omega_using [hMW, this]
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 32) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- The estimates of a 3-by-2 step of a dividend `y < 2^32 m`, for the top
three words `U = ⌊y P / 2^(K + 32)⌋` of `y P` and the top two
`D = ⌊m P / 2^(K + 32)⌋ ≥ 2^31` of `m P`: `U < (2^32 + 1) D`; `quot`'s 2-by-1
estimate `min(⌊⌊U / 2^32⌋ / ⌊D / 2^32⌋⌋, 2^32 - 1)` is within 2 above
`Q = min(⌊U / D⌋, 2^32 - 1)` (`WordStep32.quot_le_div`, `WordStep32.div_le_quot`);
and `q ≤ Q ≤ q + 1` for `q = ⌊y / m⌋` (`qhat_trunc`). -/
theorem qhat3_div {Y M P K : Nat} (hP : 0 < P) (hYM : Y < M * 2 ^ 32)
    (hd : 2 ^ 31 ≤ M * P / 2 ^ (K + 32) / 2 ^ 32) :
    Y * P / 2 ^ (K + 32) < (2 ^ 32 + 1) * (M * P / 2 ^ (K + 32)) ∧
      min (Y * P / 2 ^ (K + 32) / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ≤
        min (Y * P / 2 ^ (K + 32) / 2 ^ 32 / (M * P / 2 ^ (K + 32) / 2 ^ 32)) (2 ^ 32 - 1) ∧
      min (Y * P / 2 ^ (K + 32) / 2 ^ 32 / (M * P / 2 ^ (K + 32) / 2 ^ 32)) (2 ^ 32 - 1) ≤
        min (Y * P / 2 ^ (K + 32) / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) + 2 ∧
      Y / M ≤ min (Y * P / 2 ^ (K + 32) / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ∧
      min (Y * P / 2 ^ (K + 32) / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ≤ Y / M + 1 := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hYM; exact Nat.not_lt_zero _ hYM
  have hBK : (2 : Nat) ^ (K + 32) = 2 ^ K * 2 ^ 32 := Nat.pow_add _ _ _
  have hq0 : Y * P / (M * P) = Y / M := Nat.mul_div_mul_right _ _ hP
  have hq : Y * P / (M * P) < 2 ^ 32 := by
    rw [hq0, Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 32) M]; exact hYM
  generalize hD : M * P / 2 ^ (K + 32) = D at hd ⊢
  have hD32 : 2 ^ 32 ≤ D := by
    have := Nat.mul_le_mul_right (2 ^ 32) hd
    have h2 := Nat.div_mul_le_self D (2 ^ 32)
    have h3 : 2 ^ 31 * 2 ^ 32 = 2 ^ 63 := by rw [← Nat.pow_add]
    omega_using [this, h2, h3]
  have tr := qhat_trunc (Y := Y * P) (N := M * P) (K := K + 32) hq (by rw [hD]; exact hD32)
  rw [hD, hq0] at tr
  generalize hU : Y * P / 2 ^ (K + 32) = U at tr ⊢
  -- `y P < 2^32 m P < 2^32 (D + 1) 2^(K + 32)`, so `U < (D + 1) 2^32 ≤ (2^32 + 1) D`.
  have hUD : U < (2 ^ 32 + 1) * D := by
    have h1 : Y * P < (D + 1) * 2 ^ (K + 32) * 2 ^ 32 := by
      have := lt_succ_div_mul (M * P) (2 ^ (K + 32)) (Nat.two_pow_pos _)
      rw [hD] at this
      have h3 : Y * P < M * P * 2 ^ 32 := by
        rw [Nat.mul_assoc, Nat.mul_comm P, ← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right hYM hP
      exact Nat.lt_of_lt_of_le h3 (Nat.mul_le_mul_right _ (Nat.le_of_lt this))
    have h2 : U < (D + 1) * 2 ^ 32 := by
      rw [← hU, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_assoc, Nat.mul_comm (2 ^ 32),
        ← Nat.mul_assoc]; exact h1
    have e1 : (D + 1) * 2 ^ 32 = D * 2 ^ 32 + 2 ^ 32 := by rw [Nat.add_mul, Nat.one_mul]
    have e2 : (2 ^ 32 + 1) * D = D * 2 ^ 32 + D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega_using [h2, e1, e2, hD32]
  have hd0 : 0 < D / 2 ^ 32 := by omega_using [hd]
  have hUe : U = U / 2 ^ 32 * 2 ^ 32 + U % 2 ^ 32 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hDe : D = D / 2 ^ 32 * 2 ^ 32 + D % 2 ^ 32 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hle1 : U / D ≤ U / 2 ^ 32 / (D / 2 ^ 32) := by
    have := quot_le_div (N := U / 2 ^ 32) (ml := D % 2 ^ 32) (Nat.mod_lt U (Nat.two_pow_pos 32)) hd0
    rwa [← hUe, ← hDe] at this
  refine ⟨hUD, Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hle1, Nat.min_le_right _ _⟩, ?_, tr.1, tr.2⟩
  rcases Nat.lt_or_ge (U / D) (2 ^ 32) with hlt | hge
  · have := div_le_quot (N := U / 2 ^ 32) (yl := U % 2 ^ 32) (Nat.mod_lt D (Nat.two_pow_pos 32)) hd
      (by rwa [← hUe, ← hDe])
    rw [← hUe, ← hDe] at this
    omega_using [this, hlt]
  · omega_using [hge]

/-- The estimates of a 3-by-2 step, for the top three words `U = ⌊x P / 2^K⌋`
of `x P` and the top two `D = ⌊m P / 2^(K + 32)⌋ ≥ 2^63` of `m P`, `x < m`:
`U < (2^32 + 1) D`; `quot`'s 2-by-1 estimate `min(⌊⌊U / 2^32⌋ / ⌊D / 2^32⌋⌋, 2^32 - 1)`
is within 2 above `Q = min(⌊U / D⌋, 2^32 - 1)` (`WordStep32.quot_le_div`,
`WordStep32.div_le_quot`); and `q ≤ Q ≤ q + 1` for `q = ⌊x 2^32 / m⌋`
(`qhat_trunc`). -/
theorem qhat3_norm {X M P K : Nat} (hP : 0 < P) (hXM : X < M)
    (hd : 2 ^ 31 ≤ M * P / 2 ^ (K + 32) / 2 ^ 32) :
    X * P / 2 ^ K < (2 ^ 32 + 1) * (M * P / 2 ^ (K + 32)) ∧
      min (X * P / 2 ^ K / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ≤
        min (X * P / 2 ^ K / 2 ^ 32 / (M * P / 2 ^ (K + 32) / 2 ^ 32)) (2 ^ 32 - 1) ∧
      min (X * P / 2 ^ K / 2 ^ 32 / (M * P / 2 ^ (K + 32) / 2 ^ 32)) (2 ^ 32 - 1) ≤
        min (X * P / 2 ^ K / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) + 2 ∧
      X * 2 ^ 32 / M ≤ min (X * P / 2 ^ K / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ∧
      min (X * P / 2 ^ K / (M * P / 2 ^ (K + 32))) (2 ^ 32 - 1) ≤ X * 2 ^ 32 / M + 1 := by
  have hM0 : 0 < M := by omega_using [hXM]
  have hBK : (2 : Nat) ^ (K + 32) = 2 ^ K * 2 ^ 32 := Nat.pow_add _ _ _
  have hq0 : X * P * 2 ^ 32 / (M * P) = X * 2 ^ 32 / M := by
    rw [Nat.mul_assoc, Nat.mul_comm P, ← Nat.mul_assoc, Nat.mul_div_mul_right _ _ hP]
  have hq : X * P * 2 ^ 32 / (M * P) < 2 ^ 32 := by
    rw [hq0, Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 32) M]
    exact Nat.mul_lt_mul_of_pos_right hXM (Nat.two_pow_pos 32)
  have hYU : X * P * 2 ^ 32 / 2 ^ (K + 32) = X * P / 2 ^ K := by
    rw [hBK, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 32)]
  generalize hD : M * P / 2 ^ (K + 32) = D at hd ⊢
  have hD32 : 2 ^ 32 ≤ D := by
    have := Nat.mul_le_mul_right (2 ^ 32) hd
    have h2 := Nat.div_mul_le_self D (2 ^ 32)
    have h3 : 2 ^ 31 * 2 ^ 32 = 2 ^ 63 := by rw [← Nat.pow_add]
    omega_using [this, h2, h3]
  have tr := qhat_trunc (Y := X * P * 2 ^ 32) (N := M * P) (K := K + 32) hq
    (by rw [hD]; exact hD32)
  rw [hYU, hD, hq0] at tr
  generalize hU : X * P / 2 ^ K = U at tr ⊢
  -- `x P < m P < (D + 1) 2^(K + 32)`, so `U < (D + 1) 2^32 ≤ (2^32 + 1) D`.
  have hUD : U < (2 ^ 32 + 1) * D := by
    have h1 : X * P < (D + 1) * 2 ^ (K + 32) := by
      have := lt_succ_div_mul (M * P) (2 ^ (K + 32)) (Nat.two_pow_pos _)
      rw [hD] at this
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hXM hP) (Nat.le_of_lt this)
    have h2 : U < (D + 1) * 2 ^ 32 := by
      rw [← hU, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K), Nat.mul_assoc, Nat.mul_comm (2 ^ 32), ← hBK]; exact h1
    have e1 : (D + 1) * 2 ^ 32 = D * 2 ^ 32 + 2 ^ 32 := by rw [Nat.add_mul, Nat.one_mul]
    have e2 : (2 ^ 32 + 1) * D = D * 2 ^ 32 + D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega_using [h2, e1, e2, hD32]
  have hd0 : 0 < D / 2 ^ 32 := by omega_using [hd]
  have hUe : U = U / 2 ^ 32 * 2 ^ 32 + U % 2 ^ 32 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hDe : D = D / 2 ^ 32 * 2 ^ 32 + D % 2 ^ 32 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hle1 : U / D ≤ U / 2 ^ 32 / (D / 2 ^ 32) := by
    have := quot_le_div (N := U / 2 ^ 32) (ml := D % 2 ^ 32) (Nat.mod_lt U (Nat.two_pow_pos 32)) hd0
    rwa [← hUe, ← hDe] at this
  refine ⟨hUD, Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hle1, Nat.min_le_right _ _⟩, ?_, tr.1, tr.2⟩
  rcases Nat.lt_or_ge (U / D) (2 ^ 32) with hlt | hge
  · have := div_le_quot (N := U / 2 ^ 32) (yl := U % 2 ^ 32) (Nat.mod_lt D (Nat.two_pow_pos 32)) hd
      (by rwa [← hUe, ← hDe])
    rw [← hUe, ← hDe] at this
    omega_using [this, hlt]
  · omega_using [hge]

/-- The corrections of a 3-by-2 estimate `q̂₀` of `Q = min(⌊U / D⌋, 2^32 - 1)`,
`Q ≤ q̂₀ ≤ Q + 2`, for `U < (2^32 + 1) D`: `t₁ = U - q̂₀ D` modulo `W > 8 D`
(with its borrow `b`), and `D` added to it if its top half is set (with the
carry `c`): `q̂₀` is `Q` plus one for each of `t₁` and `t₂` whose top half is
set. -/
theorem quot3_val {W U D q0 T1 T2 b c : Nat} (hD0 : 0 < D) (hDW : 4 * D < W / 2)
    (hUD : U < (2 ^ 32 + 1) * D) (hge : min (U / D) (2 ^ 32 - 1) ≤ q0)
    (hle : q0 ≤ min (U / D) (2 ^ 32 - 1) + 2) (hq0 : q0 < 2 ^ 32)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + q0 * D = U + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then D else 0) :
    q0 = min (U / D) (2 ^ 32 - 1) + (if W / 2 ≤ T1 then 1 else 0) + (if W / 2 ≤ T2 then 1 else 0) := by
  have hy := Nat.div_add_mod U D
  have hr := Nat.mod_lt U hD0
  -- `q̂₀ = Q + j`; for `j > 0`, `Q = ⌊U / D⌋`.
  obtain ⟨j, hj, hqj, hQ⟩ : ∃ j, j ≤ 2 ∧ q0 = min (U / D) (2 ^ 32 - 1) + j ∧
      (0 < j → min (U / D) (2 ^ 32 - 1) = U / D) :=
    ⟨q0 - min (U / D) (2 ^ 32 - 1), by omega_using [hle], by omega_using [hge], by omega_using [hq0]⟩
  generalize hQd : min (U / D) (2 ^ 32 - 1) = Q at hqj hQ ⊢
  have hQU : Q * D ≤ U := by
    have := Nat.min_le_left (U / D) (2 ^ 32 - 1)
    rw [hQd] at this
    exact Nat.le_trans (Nat.mul_le_mul_right D this) (Nat.div_mul_le_self U D)
  -- `U - Q D < 2 D`: `U - ⌊U / D⌋ D < D`, else `Q = 2^32 - 1` and `U < (2^32 + 1) D`.
  have hQ2 : U < Q * D + 2 * D := by
    rcases Nat.lt_or_ge (U / D) (2 ^ 32 - 1) with h | h
    · have : Q = U / D := by rw [← hQd]; exact Nat.min_eq_left (Nat.le_of_lt h)
      subst this
      have : U / D * D + U % D = U := by rw [Nat.mul_comm]; exact hy
      omega_using [this, hr]
    · have : Q = 2 ^ 32 - 1 := by rw [← hQd]; exact Nat.min_eq_right h
      subst this
      have e : (2 ^ 32 + 1) * D = (2 ^ 32 - 1) * D + 2 * D := by rw [← Nat.add_mul]
      omega_using [hUD, e]
  have hq0D : q0 * D = Q * D + j * D := by rw [hqj, Nat.add_mul]
  -- `U - q̂₀ D` and `U - q̂₀ D + D` in two's complement.
  have hv1 : -((W : Int) / 2) ≤ (U : Int) - (q0 * D : Nat) := by
    rw [hq0D]; push_cast
    have : j * D ≤ 2 * D := Nat.mul_le_mul_right D hj
    omega_arith
  have hv2 : (U : Int) - (q0 * D : Nat) < (W : Int) / 2 := by
    rw [hq0D]; push_cast; omega_arith
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hw1 : -((W : Int) / 2) ≤ addIfNeg D ((U : Int) - (q0 * D : Nat)) := by
    unfold addIfNeg; split <;> omega_using [hv1]
  have hw2 : addIfNeg D ((U : Int) - (q0 * D : Nat)) < (W : Int) / 2 := by
    unfold addIfNeg; split <;> omega_arith
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, e1]
  simp only [twos_neg hv1 hv2, twos_neg hw1 hw2]
  unfold addIfNeg
  rw [hq0D]
  have hUQ : U = Q * D + (U - Q * D) := by omega_using [hQU]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega_using [hj]) with rfl | rfl | rfl
  · simp only [Nat.zero_mul, Nat.add_zero] at hqj ⊢
    have : ¬ (U : Int) - (Q * D : Nat) < 0 := by push_cast; omega_arith
    simp only [this, ite_false, Int.add_zero]; omega_using [hqj]
  · have hQe := hQ (by decide)
    have hlt : U < Q * D + D := by
      rw [hQe]; have : U / D * D + U % D = U := by rw [Nat.mul_comm]; exact hy
      omega_using [this, hr]
    have a1 : (U : Int) - (Q * D + 1 * D : Nat) < 0 := by push_cast; omega_arith
    have a2 : ¬ (U : Int) - (Q * D + 1 * D : Nat) + D < 0 := by push_cast; omega_arith
    simp only [a1, ite_true, a2, ite_false]; omega_using [hqj]
  · have hQe := hQ (by decide)
    have hlt : U < Q * D + D := by
      rw [hQe]; have : U / D * D + U % D = U := by rw [Nat.mul_comm]; exact hy
      omega_using [this, hr]
    have a1 : (U : Int) - (Q * D + 2 * D : Nat) < 0 := by push_cast; omega_arith
    have a2 : (U : Int) - (Q * D + 2 * D : Nat) + D < 0 := by push_cast; omega_arith
    simp only [a1, ite_true, a2]; omega_using [hqj]

end VG.Proof.Bignum.WordStep32
