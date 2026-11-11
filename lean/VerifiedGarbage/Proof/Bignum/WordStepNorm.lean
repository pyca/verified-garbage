module
-- separate module: target-independent, for every target's word steps of `R² mod n` (PPC64LE's now)
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep

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
  while it is negative is `x 2^64 mod m`, for any such `q̂`.
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

end VG.Proof.Bignum.WordStep
