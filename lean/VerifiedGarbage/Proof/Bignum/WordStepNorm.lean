module
-- separate module: target-independent, for every target's word steps of `R² mod n` (PPC64LE's now)
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.WordStep

/-!
# Multiword arithmetic: a step of long division by a normalized estimate

The arithmetic of `x := x 2^64 mod m` by a step of long division (Knuth,
TAOCP vol. 2, §4.3.1, Algorithm D) for any `m`, whose top word need not have
its top bit set, independent of the target. `q̂` is estimated from the top
words of `x P` and `m P` for a power of two `P` (Knuth's normalization), but
`x 2^64 - q̂ m` is computed from `x` and `m` themselves:

* `shift_floor`: the top words of `x P`, from those of `x`;
* `qhat_norm`: the estimate from `x P` and `m P` is `q ≤ q̂ ≤ q + 2` for
  `q = ⌊x 2^64 / m⌋` (`WordStep.qhat_ge`, `WordStep.qhat_le`);
* `wordStepQ_val`: `x 2^64 - q̂ m` in two's complement with `m` added twice
  while it is negative is `x 2^64 mod m`, for any such `q̂`;
* `qhat_trunc`: an estimate from the top three words of the dividend and the
  top two of the divisor (above the same power of two) is `q ≤ q̂ ≤ q + 1`,
  and `wordStepQ1_val`: then `m` added once if negative is `x 2^64 mod m`.
-/

@[expose] public section

namespace VG.Proof.Bignum.WordStep

/-- `⌊(a 2^z + r) / 2^64⌋ = ⌊a 2^z / 2^64⌋` for `r < 2^z ≤ 2^64`. -/
theorem div_pow_add {a r z : Nat} (hz : z ≤ 64) (hr : r < 2 ^ z) :
    (a * 2 ^ z + r) / 2 ^ 64 = a * 2 ^ z / 2 ^ 64 := by
  have e : (2 : Nat) ^ 64 = 2 ^ z * 2 ^ (64 - z) := by rw [← Nat.pow_add]; congr 1; omega_using [hz]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_comm a, Nat.mul_add_div (Nat.two_pow_pos z),
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos z), Nat.div_eq_of_lt hr, Nat.add_zero]

/-- The top words of `x P` for `P = 2^z`, `z ≤ 64`: `⌊(a 2^K + l) P / 2^(K + 64)⌋ =
⌊a P / 2^64⌋` for `l < 2^K`. -/
theorem shift_floor {a l K z : Nat} (hz : z ≤ 64) (hl : l < 2 ^ K) :
    (a * 2 ^ K + l) * 2 ^ z / 2 ^ (K + 64) = a * 2 ^ z / 2 ^ 64 := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ K) (2 ^ z),
    ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos K), Nat.add_comm]
  refine div_pow_add hz ?_
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K), Nat.mul_comm (2 ^ z)]
  exact Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos z)

/-- The top word of `(a 2^(K + 64) + b 2^K + l) 2^z` above `2^(K + 64)`, for
`l < 2^K` and `z ≤ 64`: `a 2^z + ⌊b 2^z / 2^64⌋`. -/
theorem top_shift {a b l K z : Nat} (hz : z ≤ 64) (hl : l < 2 ^ K) :
    (a * 2 ^ (K + 64) + b * 2 ^ K + l) * 2 ^ z / 2 ^ (K + 64) = a * 2 ^ z + b * 2 ^ z / 2 ^ 64 := by
  rw [Nat.add_assoc, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ (K + 64)), ← Nat.mul_assoc,
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), shift_floor hz hl, Nat.add_comm]

/-- `a 2^z + f < 2^64` for `a 2^z < 2^64` and `f < 2^z`: the low bits of a
word shifted left are free. -/
theorem shl_add_lt {a f z : Nat} (hz : z ≤ 64) (h : a * 2 ^ z < 2 ^ 64) (hf : f < 2 ^ z) :
    a * 2 ^ z + f < 2 ^ 64 := by
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - z) * 2 ^ z := by rw [← Nat.pow_add]; congr 1; omega_using [hz]
  rw [e] at h ⊢
  have ha : a < 2 ^ (64 - z) := Nat.lt_of_mul_lt_mul_right h
  have := Nat.mul_le_mul_right (2 ^ z) (show a + 1 ≤ 2 ^ (64 - z) by omega_using [ha])
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_using [this, hf]

/-- The estimate `q̂ = min(⌊u / d⌋, 2^64 - 1)` from the top two words `u` of
`x P` (above `2^K`) and the top word `d ≥ 2^63` of `m P` (above `2^(K + 64)`)
is `q ≤ q̂ ≤ q + 2`, for `q = ⌊x 2^64 / m⌋` and `x < m`. -/
theorem qhat_norm {X M P K : Nat} (hP : 0 < P) (hXM : X < M)
    (hd : 2 ^ 63 ≤ M * P / 2 ^ (K + 64)) :
    X * 2 ^ 64 / M ≤ min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ∧
      min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ≤ X * 2 ^ 64 / M + 2 := by
  have hM0 : 0 < M := by omega_using [hXM]
  have hBK : (2 : Nat) ^ (K + 64) = 2 ^ K * 2 ^ 64 := Nat.pow_add _ _ _
  -- `y = x P 2^64 = u 2^(K + 64) + yₗ` and `m P = d 2^(K + 64) + mₗ`.
  have hY : X * P * 2 ^ 64 = X * P / 2 ^ K * 2 ^ (K + 64) + X * P % 2 ^ K * 2 ^ 64 := by
    rw [hBK, ← Nat.mul_assoc, ← Nat.add_mul, Nat.mul_comm (X * P / 2 ^ K), Nat.div_add_mod]
  have hYl : X * P % 2 ^ K * 2 ^ 64 < 2 ^ (K + 64) := by
    rw [hBK]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos K)) (Nat.two_pow_pos 64)
  have hMd : M * P = M * P / 2 ^ (K + 64) * 2 ^ (K + 64) + M * P % 2 ^ (K + 64) := by
    rw [Nat.mul_comm (M * P / _), Nat.div_add_mod]
  have hq0 : X * P * 2 ^ 64 / (M * P) = X * 2 ^ 64 / M := by
    rw [Nat.mul_assoc, Nat.mul_comm P, ← Nat.mul_assoc, Nat.mul_div_mul_right _ _ hP]
  have hq : X * P * 2 ^ 64 / (M * P) < 2 ^ 64 := by
    rw [hq0, Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 64) M]
    exact Nat.mul_lt_mul_of_pos_right hXM (Nat.two_pow_pos 64)
  rw [hY, hMd] at hq
  have hge := qhat_ge hYl (by omega_using [hd]) hq
  have hle := qhat_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hd hq
  rw [← hY, ← hMd, hq0] at hge hle
  exact ⟨hge, hle⟩

/-- A step of long division over the words, for any estimate `q ≤ q̂ ≤ q + 2`
of `q = ⌊x 2^64 / m⌋`: `t₁ = x 2^64 - q̂ m` modulo `W > 8 m` (with its borrow
`b`) and `m` added twice to it while its top half is set (with the carries
`c₁`, `c₂`) is `x 2^64 mod m`. -/
theorem wordStepQ_val {W X M qh T1 T2 T3 b c1 c2 : Nat} (hM0 : 0 < M) (hMW : 4 * M < W / 2)
    (hge : X * 2 ^ 64 / M ≤ qh) (hle : qh ≤ X * 2 ^ 64 / M + 2)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = X * 2 ^ 64 + W * b)
    (hT2 : T2 < W) (hc1 : c1 < 2) (h2 : T2 + W * c1 = T1 + if W / 2 ≤ T1 then M else 0)
    (hT3 : T3 < W) (hc2 : c2 < 2) (h3 : T3 + W * c2 = T2 + if W / 2 ≤ T2 then M else 0) :
    T3 = X * 2 ^ 64 % M := by
  obtain ⟨hfin, hv1, hv2, hw1, hw2⟩ := addBack_two (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc1 h2
  have hv1' : -((W : Int) / 2) ≤ addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) := by
    rw [hfin]; omega_using []
  have hv2' : addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 64) hM0; omega_using [hMW, this]
  have e3 := twos_of_add hw1 hw2 hv1' hv2' e2 hT3 hc2 h3
  rw [e3, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 64) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- The estimate as restoring division makes it, all ones when the top word
`u₂` of the dividend is the divisor `d`: `min(⌊u / d⌋, 2^64 - 1)` for
`u = u₂ 2^64 + u₁`, `u₂ ≤ d`. -/
theorem qhat_fix {u2 u1 d : Nat} (hd0 : 0 < d) (hu2 : u2 ≤ d) (hu1 : u1 < 2 ^ 64) :
    (if u2 = d then 2 ^ 64 - 1 else (u2 * 2 ^ 64 + u1) / d) = min ((u2 * 2 ^ 64 + u1) / d) (2 ^ 64 - 1) := by
  by_cases h : u2 = d
  · subst h
    simp only [ite_true]
    rw [Nat.min_eq_right]
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left u2 (show 2 ^ 64 - 1 ≤ 2 ^ 64 by omega_using [])
    rw [Nat.mul_comm (2 ^ 64 - 1)]; omega_using [this]
  · have hd : u2 < d := Nat.lt_of_le_of_ne hu2 h
    simp only [h, ite_false]
    rw [Nat.min_eq_left]
    have : (u2 * 2 ^ 64 + u1) / d < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hd])]
      have := Nat.mul_le_mul_right (2 ^ 64) (show u2 + 1 ≤ d by omega_using [hd])
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm d] at this; omega_using [this, hu1]
    omega_using [this]

/-! ## A 3-by-2 estimate, one add-back -/

theorem lt_succ_div_mul (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  omega

/-- An estimate of `⌊Y / N⌋ < 2^64` from `Y` and `N` cut at `2^K`, whose top
`⌊N / 2^K⌋` is at least `2^64`: `q ≤ min(⌊⌊Y / 2^K⌋ / ⌊N / 2^K⌋⌋, 2^64 - 1) ≤ q + 1`. -/
theorem qhat_trunc {Y N K : Nat} (hq : Y / N < 2 ^ 64) (hD : 2 ^ 64 ≤ N / 2 ^ K) :
    Y / N ≤ min (Y / 2 ^ K / (N / 2 ^ K)) (2 ^ 64 - 1) ∧
      min (Y / 2 ^ K / (N / 2 ^ K)) (2 ^ 64 - 1) ≤ Y / N + 1 := by
  have hK := Nat.two_pow_pos K
  have hD0 : 0 < N / 2 ^ K := by omega
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hD0
  generalize hq' : Y / N = q at hq
  generalize hU : Y / 2 ^ K = U
  generalize hDd : N / 2 ^ K = D at hD hD0
  have hNd : D * 2 ^ K ≤ N := by rw [← hDd]; exact Nat.div_mul_le_self N _
  have hN1 : N < (D + 1) * 2 ^ K := by rw [← hDd]; exact lt_succ_div_mul _ _ hK
  have hUY : U * 2 ^ K ≤ Y := by rw [← hU]; exact Nat.div_mul_le_self Y _
  have hY1 : Y < (U + 1) * 2 ^ K := by rw [← hU]; exact lt_succ_div_mul _ _ (by omega)
  have hqN : q * N ≤ Y := by rw [← hq']; exact Nat.div_mul_le_self Y N
  have hYq : Y < (q + 1) * N := by rw [← hq']; exact lt_succ_div_mul _ _ (by omega)
  constructor
  · refine Nat.le_min.mpr ⟨?_, by omega⟩
    rw [Nat.le_div_iff_mul_le hD0]
    -- `q D 2^K ≤ q N ≤ Y`, so `q D ≤ U`.
    have h1 : q * D * 2 ^ K ≤ Y := by
      rw [Nat.mul_assoc]; exact Nat.le_trans (Nat.mul_le_mul_left q hNd) hqN
    have h2 : q * D < U + 1 := by
      have := Nat.lt_of_le_of_lt h1 hY1
      exact Nat.lt_of_mul_lt_mul_right this
    omega
  · refine Nat.le_trans (Nat.min_le_left _ _) ?_
    -- `q̂ D ≤ U`, `U 2^K ≤ Y < (q + 1) N < (q + 1) (D + 1) 2^K`.
    refine Nat.le_of_not_lt fun hc => ?_
    have hge : q + 2 ≤ U / D := by omega
    have h1 : (q + 2) * D ≤ U := Nat.le_trans (Nat.mul_le_mul_right D hge) (Nat.div_mul_le_self U D)
    have h2 : U < (q + 1) * (D + 1) := by
      have h3 : U * 2 ^ K < (q + 1) * (D + 1) * 2 ^ K := by
        rw [Nat.mul_assoc]
        exact Nat.lt_of_le_of_lt hUY (Nat.lt_of_lt_of_le hYq (Nat.mul_le_mul_left _ (Nat.le_of_lt hN1)))
      exact Nat.lt_of_mul_lt_mul_right h3
    have e1 : (q + 2) * D = (q + 1) * D + D := by rw [Nat.add_mul, Nat.add_mul (q) 1, Nat.one_mul]; omega
    have e2 : (q + 1) * (D + 1) = (q + 1) * D + (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
    omega

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

/-- A step of long division over the words, for any estimate `q ≤ q̂ ≤ q + 1`
of `q = ⌊x 2^64 / m⌋`: `t₁ = x 2^64 - q̂ m` modulo `W > 4 m` (with its borrow
`b`) and `m` added once to it if its top half is set (with the carry `c`) is
`x 2^64 mod m`. -/
theorem wordStepQ1_val {W X M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : X * 2 ^ 64 / M ≤ qh) (hle : qh ≤ X * 2 ^ 64 / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = X * 2 ^ 64 + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = X * 2 ^ 64 % M := by
  obtain ⟨hfin, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hw1 : -((W : Int) / 2) ≤ addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat)) := by
    rw [hfin]; omega_using []
  have hw2 : addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat)) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 64) hM0; omega_using [hMW, this]
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 64) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

end VG.Proof.Bignum.WordStep
