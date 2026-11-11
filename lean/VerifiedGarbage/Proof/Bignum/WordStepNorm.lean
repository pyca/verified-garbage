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
  and `wordStepQ1_div`: then `m` added once if negative is `y mod m`, for any
  dividend `y < 2^64 m` (`wordStepQ1_val` for `y = x 2^64`);
* `qhat3_div`, `quot3_val`: that estimate from `qhat_norm`'s, corrected by
  `U - q̂ D` over three words (Knuth's step D3), for any dividend
  `y < 2^64 m` (`qhat3_norm` for `y = x 2^64`), and `shift_u`: a word `u`
  below `x` in `y = x 2^64 + u` changes none of `U`'s words when they are
  above it;
* `norm_inv_step`, `norm_unique`: the shift `P` of a word's normalization,
  a step at a time, and that it is unique.
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

/-- The top two words of `(a 2^(K + 128) + b 2^(K + 64) + c 2^K + l) 2^z`
above `2^(K + 64)`, for `l < 2^K` and `z ≤ 64`: `a 2^z 2^64 + b 2^z + ⌊c 2^z /
2^64⌋`. -/
theorem top3_shift {a b c l K z : Nat} (hz : z ≤ 64) (hl : l < 2 ^ K) :
    (a * 2 ^ (K + 64 + 64) + b * 2 ^ (K + 64) + c * 2 ^ K + l) * 2 ^ z / 2 ^ (K + 64) =
      a * 2 ^ z * 2 ^ 64 + (b * 2 ^ z + c * 2 ^ z / 2 ^ 64) := by
  have : a * 2 ^ (K + 64 + 64) + b * 2 ^ (K + 64) = (a * 2 ^ 64 + b) * 2 ^ (K + 64) := by
    rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm 64 (K + 64)]
  rw [this, top_shift hz hl, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc, Nat.add_assoc]

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

/-- A step of normalization on `x = T 2^j`, `p = 2^j`: `j` grows while `x`'s top
bit is clear: the shift `P = 2^j` of a word `T`'s normalization. -/
theorem norm_inv_step {x p : BitVec 64} {T j i : Nat} (hj : j ≤ i) (hi : i < 63) (hp : p.toNat = 2 ^ j)
    (hx : x.toNat = T * 2 ^ j) (hc : j = i ∨ 2 ^ 63 ≤ T * 2 ^ j) :
    ∃ j' ≤ i + 1, (if x.toNat < 2 ^ 63 then p + p else p).toNat = 2 ^ j' ∧
      (if x.toNat < 2 ^ 63 then x + x else x).toNat = T * 2 ^ j' ∧ (j' = i + 1 ∨ 2 ^ 63 ≤ T * 2 ^ j') := by
  by_cases h : x.toNat < 2 ^ 63
  · simp only [h, ite_true]
    have hji : j = i := by omega_using [hc, h, hx]
    have hpj : 2 ^ j ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega_using [hji, hi])
    refine ⟨j + 1, by omega_using [hj], ?_, ?_, Or.inl (by omega_using [hji])⟩
    · have e2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ, Nat.mul_two]
      rw [BitVec.toNat_add, hp, e2]
      generalize 2 ^ j = a at hpj ⊢
      omega_using [hpj]
    · have e2 : T * 2 ^ (j + 1) = T * 2 ^ j + T * 2 ^ j := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      rw [BitVec.toNat_add, hx, e2]
      rw [hx] at h
      generalize T * 2 ^ j = a at h ⊢
      omega_using [h]
  · simp only [h, ite_false]
    exact ⟨j, by omega_using [hj], hp, hx, Or.inr (by omega_using [h, hx])⟩

/-- The normalization shift is unique: at most one `z` puts `⌊M 2^z / B⌋` in
`[2^63, 2^64)`. -/
theorem norm_unique {M B a b : Nat} (ha : 2 ^ 63 ≤ M * 2 ^ a / B) (ha' : M * 2 ^ a / B < 2 ^ 64)
    (hb : 2 ^ 63 ≤ M * 2 ^ b / B) (hb' : M * 2 ^ b / B < 2 ^ 64) : a = b := by
  have key : ∀ {a b : Nat}, a < b → 2 * (M * 2 ^ a / B) ≤ M * 2 ^ b / B := fun {a b} h => by
    refine Nat.le_trans (Nat.mul_div_le_mul_div_assoc 2 _ B) (Nat.div_le_div_right ?_)
    rw [← Nat.mul_assoc, Nat.mul_comm 2 M, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.pow_succ]
    exact Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by decide) h)
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := key h; omega_using [this, ha, hb']
  · exact h
  · have := key h; omega_using [this, hb, ha']

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

/-- A step of long division over the words of a dividend `y < 2^64 m`, for
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

/-- `wordStepQ1_div` for the dividend `y = x 2^64`. -/
theorem wordStepQ1_val {W X M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : X * 2 ^ 64 / M ≤ qh) (hle : qh ≤ X * 2 ^ 64 / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = X * 2 ^ 64 + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = X * 2 ^ 64 % M :=
  wordStepQ1_div hM0 hMW hge hle hT1 hb h1 hT2 hc h2

/-- The estimates of a 3-by-2 step of a dividend `y < 2^64 m`, for the top
three words `U = ⌊y P / 2^(K + 64)⌋` of `y P` and the top two
`D = ⌊m P / 2^(K + 64)⌋ ≥ 2^127` of `m P`: `U < (2^64 + 1) D`; `quot`'s 2-by-1
estimate `min(⌊⌊U / 2^64⌋ / ⌊D / 2^64⌋⌋, 2^64 - 1)` is within 2 above
`Q = min(⌊U / D⌋, 2^64 - 1)` (`WordStep.quot_le_div`, `WordStep.div_le_quot`);
and `q ≤ Q ≤ q + 1` for `q = ⌊y / m⌋` (`qhat_trunc`). -/
theorem qhat3_div {Y M P K : Nat} (hP : 0 < P) (hYM : Y < M * 2 ^ 64)
    (hd : 2 ^ 63 ≤ M * P / 2 ^ (K + 64) / 2 ^ 64) :
    Y * P / 2 ^ (K + 64) < (2 ^ 64 + 1) * (M * P / 2 ^ (K + 64)) ∧
      min (Y * P / 2 ^ (K + 64) / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ≤
        min (Y * P / 2 ^ (K + 64) / 2 ^ 64 / (M * P / 2 ^ (K + 64) / 2 ^ 64)) (2 ^ 64 - 1) ∧
      min (Y * P / 2 ^ (K + 64) / 2 ^ 64 / (M * P / 2 ^ (K + 64) / 2 ^ 64)) (2 ^ 64 - 1) ≤
        min (Y * P / 2 ^ (K + 64) / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) + 2 ∧
      Y / M ≤ min (Y * P / 2 ^ (K + 64) / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ∧
      min (Y * P / 2 ^ (K + 64) / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ≤ Y / M + 1 := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hYM; exact Nat.not_lt_zero _ hYM
  have hBK : (2 : Nat) ^ (K + 64) = 2 ^ K * 2 ^ 64 := Nat.pow_add _ _ _
  have hq0 : Y * P / (M * P) = Y / M := Nat.mul_div_mul_right _ _ hP
  have hq : Y * P / (M * P) < 2 ^ 64 := by
    rw [hq0, Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 64) M]; exact hYM
  generalize hD : M * P / 2 ^ (K + 64) = D at hd ⊢
  have hD64 : 2 ^ 64 ≤ D := by
    have := Nat.mul_le_mul_right (2 ^ 64) hd
    have h2 := Nat.div_mul_le_self D (2 ^ 64)
    have h3 : 2 ^ 63 * 2 ^ 64 = 2 ^ 127 := by rw [← Nat.pow_add]
    omega_using [this, h2, h3]
  have tr := qhat_trunc (Y := Y * P) (N := M * P) (K := K + 64) hq (by rw [hD]; exact hD64)
  rw [hD, hq0] at tr
  generalize hU : Y * P / 2 ^ (K + 64) = U at tr ⊢
  -- `y P < 2^64 m P < 2^64 (D + 1) 2^(K + 64)`, so `U < (D + 1) 2^64 ≤ (2^64 + 1) D`.
  have hUD : U < (2 ^ 64 + 1) * D := by
    have h1 : Y * P < (D + 1) * 2 ^ (K + 64) * 2 ^ 64 := by
      have := lt_succ_div_mul (M * P) (2 ^ (K + 64)) (Nat.two_pow_pos _)
      rw [hD] at this
      have h3 : Y * P < M * P * 2 ^ 64 := by
        rw [Nat.mul_assoc, Nat.mul_comm P, ← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right hYM hP
      exact Nat.lt_of_lt_of_le h3 (Nat.mul_le_mul_right _ (Nat.le_of_lt this))
    have h2 : U < (D + 1) * 2 ^ 64 := by
      rw [← hU, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_assoc, Nat.mul_comm (2 ^ 64),
        ← Nat.mul_assoc]; exact h1
    have e1 : (D + 1) * 2 ^ 64 = D * 2 ^ 64 + 2 ^ 64 := by rw [Nat.add_mul, Nat.one_mul]
    have e2 : (2 ^ 64 + 1) * D = D * 2 ^ 64 + D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega_using [h2, e1, e2, hD64]
  have hd0 : 0 < D / 2 ^ 64 := by omega_using [hd]
  have hUe : U = U / 2 ^ 64 * 2 ^ 64 + U % 2 ^ 64 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hDe : D = D / 2 ^ 64 * 2 ^ 64 + D % 2 ^ 64 := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hle1 : U / D ≤ U / 2 ^ 64 / (D / 2 ^ 64) := by
    have := quot_le_div (N := U / 2 ^ 64) (ml := D % 2 ^ 64) (Nat.mod_lt U (Nat.two_pow_pos 64)) hd0
    rwa [← hUe, ← hDe] at this
  refine ⟨hUD, Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hle1, Nat.min_le_right _ _⟩, ?_, tr.1, tr.2⟩
  rcases Nat.lt_or_ge (U / D) (2 ^ 64) with hlt | hge
  · have := div_le_quot (N := U / 2 ^ 64) (yl := U % 2 ^ 64) (Nat.mod_lt D (Nat.two_pow_pos 64)) hd
      (by rwa [← hUe, ← hDe])
    rw [← hUe, ← hDe] at this
    omega_using [this, hlt]
  · omega_using [hge]

/-- `qhat3_div` for the dividend `y = x 2^64`, `x < m`, and the top three
words `U = ⌊x P / 2^K⌋` of `x P`. -/
theorem qhat3_norm {X M P K : Nat} (hP : 0 < P) (hXM : X < M)
    (hd : 2 ^ 63 ≤ M * P / 2 ^ (K + 64) / 2 ^ 64) :
    X * P / 2 ^ K < (2 ^ 64 + 1) * (M * P / 2 ^ (K + 64)) ∧
      min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ≤
        min (X * P / 2 ^ K / 2 ^ 64 / (M * P / 2 ^ (K + 64) / 2 ^ 64)) (2 ^ 64 - 1) ∧
      min (X * P / 2 ^ K / 2 ^ 64 / (M * P / 2 ^ (K + 64) / 2 ^ 64)) (2 ^ 64 - 1) ≤
        min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) + 2 ∧
      X * 2 ^ 64 / M ≤ min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ∧
      min (X * P / 2 ^ K / (M * P / 2 ^ (K + 64))) (2 ^ 64 - 1) ≤ X * 2 ^ 64 / M + 1 := by
  have hYU : X * 2 ^ 64 * P / 2 ^ (K + 64) = X * P / 2 ^ K := by
    rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (2 ^ 64) P, ← Nat.mul_assoc,
      Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64)]
  have h := qhat3_div (Y := X * 2 ^ 64) hP (Nat.mul_lt_mul_of_pos_right hXM (Nat.two_pow_pos 64)) hd
  rw [hYU] at h
  exact h

/-- The top three words of `(x 2^64 + u) P`, `u < 2^64`, `P = 2^z ≤ 2^64`,
from `2^(K + 128)` up, are those of `x P` from `2^(K + 64)` up: the word `u`
below `x` changes none of them (`shift_floor`). -/
theorem shift_u {X u z K : Nat} (hz : z ≤ 64) (hu : u < 2 ^ 64) :
    (X * 2 ^ 64 + u) * 2 ^ z / 2 ^ (K + 128) = X * 2 ^ z / 2 ^ (K + 64) := by
  rw [show K + 128 = 64 + 64 + K by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, shift_floor hz hu,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm 64 K]

/-- The corrections of a 3-by-2 estimate `q̂₀` of `Q = min(⌊U / D⌋, 2^64 - 1)`,
`Q ≤ q̂₀ ≤ Q + 2`, for `U < (2^64 + 1) D`: `t₁ = U - q̂₀ D` modulo `W > 8 D`
(with its borrow `b`), and `D` added to it if its top half is set (with the
carry `c`): `q̂₀` is `Q` plus one for each of `t₁` and `t₂` whose top half is
set. -/
theorem quot3_val {W U D q0 T1 T2 b c : Nat} (hD0 : 0 < D) (hDW : 4 * D < W / 2)
    (hUD : U < (2 ^ 64 + 1) * D) (hge : min (U / D) (2 ^ 64 - 1) ≤ q0)
    (hle : q0 ≤ min (U / D) (2 ^ 64 - 1) + 2) (hq0 : q0 < 2 ^ 64)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + q0 * D = U + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then D else 0) :
    q0 = min (U / D) (2 ^ 64 - 1) + (if W / 2 ≤ T1 then 1 else 0) + (if W / 2 ≤ T2 then 1 else 0) := by
  have hy := Nat.div_add_mod U D
  have hr := Nat.mod_lt U hD0
  -- `q̂₀ = Q + j`; for `j > 0`, `Q = ⌊U / D⌋`.
  obtain ⟨j, hj, hqj, hQ⟩ : ∃ j, j ≤ 2 ∧ q0 = min (U / D) (2 ^ 64 - 1) + j ∧
      (0 < j → min (U / D) (2 ^ 64 - 1) = U / D) :=
    ⟨q0 - min (U / D) (2 ^ 64 - 1), by omega_using [hle], by omega_using [hge], by omega_using [hq0]⟩
  generalize hQd : min (U / D) (2 ^ 64 - 1) = Q at hqj hQ ⊢
  have hQU : Q * D ≤ U := by
    have := Nat.min_le_left (U / D) (2 ^ 64 - 1)
    rw [hQd] at this
    exact Nat.le_trans (Nat.mul_le_mul_right D this) (Nat.div_mul_le_self U D)
  -- `U - Q D < 2 D`: `U - ⌊U / D⌋ D < D`, else `Q = 2^64 - 1` and `U < (2^64 + 1) D`.
  have hQ2 : U < Q * D + 2 * D := by
    rcases Nat.lt_or_ge (U / D) (2 ^ 64 - 1) with h | h
    · have : Q = U / D := by rw [← hQd]; exact Nat.min_eq_left (Nat.le_of_lt h)
      subst this
      have : U / D * D + U % D = U := by rw [Nat.mul_comm]; exact hy
      omega_using [this, hr]
    · have : Q = 2 ^ 64 - 1 := by rw [← hQd]; exact Nat.min_eq_right h
      subst this
      have e : (2 ^ 64 + 1) * D = (2 ^ 64 - 1) * D + 2 * D := by rw [← Nat.add_mul]
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

end VG.Proof.Bignum.WordStep
