module

public import VerifiedGarbage.Impl.Ed25519.CombTable16
public import VerifiedGarbage.Proof.Ed25519.CombDigits
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A comb of one table per digit

The odd tables `combTable16` represent `[k 16 · 256^j]B`, checked as `combTable` is,
from `[16]B`; with `combTable`'s, the table of digit `i < 64` holds `[k 16^i]B`
(`combCached64_ok`). Adding every digit's `d_i 16^i` to `[17 G]B` gives the scalar's
multiple (`comb64_total`), since `17 G = 8 Σ_{i < 64} 16^i`.
-/

@[expose] public section

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519 VG.Impl.Ed25519 Edwards
open Spec.X25519 (Fe)

private theorem tables16_check :
    checkTables (pointMul 16 basePoint) (combTable16.map (·.map uncache)) = true := by
  decide +kernel

private theorem tables16_cached :
    combTable16.all (fun row => row.all fun e => decide (recache e = e)) = true := by decide +kernel

private theorem tables16_length :
    combTable16.length = 32 ∧ combTable16.all (fun row => row.length == 8) = true := by
  decide +kernel

/-- Entry `k ≤ 8` of odd table `j` is the cached `[k 16 · 256^j]B`, of a point with `Z = 1`. -/
theorem combCached16_ok (j k : Nat) (hj : j < 32) (hk : k < 9) :
    ∃ q, combCached16 j k = cache q ∧ q.Z = 1 ∧ Rep q ((k * 256 ^ j) • ((16 : Nat) • baseAff)) :=
  cachedOf_ok combTable16 _ _ (pointMul_rep 16 basePoint_rep) tables16_check tables16_cached
    tables16_length j k hj hk

/-- Entry `k ≤ 8` of the table of digit `i < 64` is the cached `[k 16^i]B`, of a point with
`Z = 1`. -/
theorem combCached64_ok (i k : Nat) (hi : i < 64) (hk : k < 9) :
    ∃ q, combCached64 i k = cache q ∧ q.Z = 1 ∧ Rep q ((k * 16 ^ i) • baseAff) := by
  unfold combCached64
  split
  · obtain ⟨q, h1, h2, h3⟩ := combCached_ok (i / 2) k (by omega) hk
    have e : 16 ^ i = 256 ^ (i / 2) := by
      rw [show (256 : Nat) = 16 ^ 2 from rfl, ← pow_mul]; congr 1; omega
    exact ⟨q, h1, h2, by rw [e]; exact h3⟩
  · obtain ⟨q, h1, h2, h3⟩ := combCached16_ok (i / 2) k (by omega) hk
    have e : k * 16 ^ i = k * 256 ^ (i / 2) * 16 := by
      rw [show (256 : Nat) = 16 ^ 2 from rfl, ← pow_mul, Nat.mul_assoc, ← pow_succ]
      congr 2; omega
    rw [smul_smul] at h3
    exact ⟨q, h1, h2, by rw [e]; exact h3⟩

/-- The entry for the digit `n - 8` of the table of digit `i`, negated for a negative digit,
represents `[(n - 8) 16^i]B`, with `Z = 1`. -/
theorem combEntry64_ok (i n : Nat) (hi : i < 64) (hn : n < 16) :
    ∃ q, (if n < 8 then negCached (combCached64 i (mag n)) else combCached64 i (mag n)) = cache q ∧
      q.Z = 1 ∧ Rep q ((((n : ℤ) - 8) * 16 ^ i) • baseAff) := by
  obtain ⟨q₀, hq₀, hz, hr⟩ := combCached64_ok i (mag n) hi (mag_lt hn)
  by_cases hlt : n < 8
  · refine ⟨negPoint q₀, by simp only [hlt, ↓reduceIte]; rw [hq₀, negCached_cache], hz, ?_⟩
    have e : ((n : ℤ) - 8) * 16 ^ i = -(((mag n * 16 ^ i : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : n ≤ 8)]; ring
    rw [e, neg_smul, natCast_zsmul]
    exact hr.neg
  · refine ⟨q₀, by simp only [hlt, ↓reduceIte]; exact hq₀, hz, ?_⟩
    have e : ((n : ℤ) - 8) * 16 ^ i = (((mag n * 16 ^ i : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ n)]; ring
    rw [e, natCast_zsmul]
    exact hr

/-! ## The digits' sum -/

/-- `Σ_{i < c} d_i 16^i`. -/
def digitSum64 (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => digitSum64 S c + sdig S c * 16 ^ c

/-- `Σ_{i < c} n_i 16^i`. -/
def nibSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => nibSum S c + nib S c * 16 ^ c

theorem nibSum_eq (S : Nat) : ∀ n, nibSum S n = S % 16 ^ n
  | 0 => by simp [nibSum, Nat.mod_one]
  | n + 1 => by rw [nibSum, nibSum_eq S n, pow_succ, Nat.mod_mul, nib]; ring

/-- `Σ_{i < c} 16^i`. -/
def geom16 : Nat → Nat
  | 0 => 0
  | c + 1 => geom16 c + 16 ^ c

theorem digitSum64_eq (S : Nat) : ∀ c, digitSum64 S c = nibSum S c - 8 * geom16 c
  | 0 => rfl
  | c + 1 => by
    simp only [digitSum64, nibSum, geom16, digitSum64_eq S c, sdig]
    push_cast; ring

theorem geom16_64 : 8 * geom16 64 = 17 * combGVal := by decide

/-- The digits' multiples of `B`, added to `[17 G]B`, give the scalar: `17 G + Σ_i d_i 16^i = S`. -/
theorem comb64_total {S : Nat} (hS : S < 2 ^ 256) :
    ((17 * combGVal : Nat) : ℤ) + digitSum64 S 64 = S := by
  rw [digitSum64_eq, nibSum_eq, Nat.mod_eq_of_lt (by simpa using hS), ← geom16_64]
  push_cast; ring

end VG.Proof.Ed25519
