module

public import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent, for every architecture's word division with a quotient

/-!
# Multiword arithmetic: long division with the quotient's digits

What a step of long division (`WordStep`, Knuth's Algorithm D) leaves of the
quotient, independent of the target:

* the digit law: for the estimate `⌊y / m⌋ ≤ q̂ ≤ ⌊y / m⌋ + 1`, `y - q̂ m` is
  negative exactly when `q̂` is one too many, so the quotient's digit is `q̂`
  less one where the step adds `m` back (`digit_eq`);
* a dividend's top part `A`, a digit `a` brought down: its quotient and
  remainder from `A`'s (`div_step`, `mod_step`), and the digit below `2^64`
  (`digit_lt`).
-/

@[expose] public section

namespace VG.Proof.Bignum.LongDivision

open VG.Proof.Bignum.WordStep

/-- The digit law: `t₁ = y - q̂ m` modulo `W > 4 m` (with its borrow `b`) has
its top half set exactly when `q̂ = ⌊y / m⌋ + 1`, so `q̂`, less one if so, is
`⌊y / m⌋`. -/
theorem digit_eq {W y M qh T1 b : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : y / M ≤ qh) (hle : qh ≤ y / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = y + W * b) :
    (if W / 2 ≤ T1 then qh - 1 else qh) = y / M := by
  obtain ⟨-, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have hn := twos_neg hv1 hv2
  rw [← e1] at hn
  have hdm : y / M * M ≤ y := Nat.div_mul_le_self y M
  by_cases hneg : W / 2 ≤ T1
  · have hv : (y : Int) - (qh * M : Nat) < 0 := hn.mp hneg
    simp only [hneg, ite_true]
    have hlt : y < qh * M := by omega
    have hq : y / M < qh := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hdm hlt)
    generalize y / M = q at hq hle ⊢
    omega
  · have hv : ¬ ((y : Int) - (qh * M : Nat) < 0) := fun h => hneg (hn.mpr h)
    simp only [hneg, ite_false]
    have hq0 : qh * M ≤ y := by omega
    have hq : qh ≤ y / M := (Nat.le_div_iff_mul_le hM0).mpr hq0
    generalize y / M = q at hq hge ⊢
    omega

/-- `A 2^64 + a` as the remainder's part and a multiple of `m`. -/
theorem split_step (A a M : Nat) :
    A * 2 ^ 64 + a = (A % M * 2 ^ 64 + a) + M * (A / M * 2 ^ 64) := by
  calc A * 2 ^ 64 + a = (M * (A / M) + A % M) * 2 ^ 64 + a := by rw [Nat.div_add_mod]
    _ = (A % M * 2 ^ 64 + a) + M * (A / M * 2 ^ 64) := by rw [Nat.add_mul, Nat.mul_assoc]; omega

/-- The quotient of `A 2^64 + a` by `m`, from `A`'s: `⌊A / m⌋ 2^64` and the
digit `⌊((A mod m) 2^64 + a) / m⌋`. -/
theorem div_step (A a M : Nat) :
    (A * 2 ^ 64 + a) / M = A / M * 2 ^ 64 + (A % M * 2 ^ 64 + a) / M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  rw [split_step A a M, Nat.add_mul_div_left _ _ hM, Nat.add_comm]

/-- The remainder of `A 2^64 + a` by `m`, from `A`'s. -/
theorem mod_step (A a M : Nat) : (A * 2 ^ 64 + a) % M = (A % M * 2 ^ 64 + a) % M := by
  rw [split_step A a M, Nat.add_mul_mod_self_left]

/-- The digit is below `2^64`. -/
theorem digit_lt {R a M : Nat} (hR : R < M) (ha : a < 2 ^ 64) : (R * 2 ^ 64 + a) / M < 2 ^ 64 := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hR
  rw [Nat.div_lt_iff_lt_mul hM]
  calc R * 2 ^ 64 + a < R * 2 ^ 64 + 2 ^ 64 := by omega_using [ha]
    _ = (R + 1) * 2 ^ 64 := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ M * 2 ^ 64 := Nat.mul_le_mul_right _ hR
    _ = 2 ^ 64 * M := Nat.mul_comm _ _

/-- Normalization: `n` of `K + 1` words with its top word `t ≠ 0`, shifted
left by `t`'s leading zeros `63 - log₂ t`, has its top bit set and still
`K + 1` words. -/
theorem norm_bounds {n K : Nat} (lo : 2 ^ (64 * K) ≤ n) (hi : n < 2 ^ (64 * K) * 2 ^ 64) :
    2 ^ (64 * K) * 2 ^ 63 ≤ n * 2 ^ (63 - Nat.log2 (n / 2 ^ (64 * K))) ∧
      n * 2 ^ (63 - Nat.log2 (n / 2 ^ (64 * K))) < 2 ^ (64 * K) * 2 ^ 64 := by
  have hP := Nat.two_pow_pos (64 * K)
  generalize 2 ^ (64 * K) = P at lo hi hP
  have ht0 : n / P ≠ 0 := by
    intro h; rw [Nat.div_eq_zero_iff_lt hP] at h; omega
  have htl : n / P < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hP).mpr (by rw [Nat.mul_comm]; exact hi)
  generalize ht : n / P = t at ht0 htl
  have l1 : 2 ^ Nat.log2 t ≤ t := Nat.log2_self_le ht0
  have l2 : t < 2 ^ (Nat.log2 t + 1) := Nat.lt_log2_self
  have hlog : Nat.log2 t < 64 := by
    have := Nat.lt_of_le_of_lt l1 htl
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  generalize hz : 63 - Nat.log2 t = z
  have e63 : 2 ^ Nat.log2 t * 2 ^ z = 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega
  have e64 : 2 ^ (Nat.log2 t + 1) * 2 ^ z = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have hd : n = t * P + n % P := by rw [← ht]; exact (Nat.div_add_mod' n P).symm
  have hr : n % P < P := Nat.mod_lt _ hP
  have tz1 : 2 ^ 63 ≤ t * 2 ^ z := by rw [← e63]; exact Nat.mul_le_mul_right _ l1
  have tz2 : (t + 1) * 2 ^ z ≤ 2 ^ 64 := by rw [← e64]; exact Nat.mul_le_mul_right _ l2
  constructor
  · calc P * 2 ^ 63 ≤ P * (t * 2 ^ z) := Nat.mul_le_mul_left _ tz1
      _ = t * P * 2 ^ z := by rw [Nat.mul_comm P, Nat.mul_right_comm]
      _ ≤ n * 2 ^ z := Nat.mul_le_mul_right _ (by omega)
  · calc n * 2 ^ z = (t * P + n % P) * 2 ^ z := by rw [← hd]
      _ < (t * P + P) * 2 ^ z := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = P * ((t + 1) * 2 ^ z) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_comm t P, Nat.mul_assoc]
      _ ≤ P * 2 ^ 64 := Nat.mul_le_mul_left _ tz2

end VG.Proof.Bignum.LongDivision
