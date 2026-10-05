import VerifiedGarbage.Proof.Ocb.Spec

/-!
# `ntz` as the lowest set bit

A positive `n` is `2^ntz(n)` times an odd number (`ntz_spec`), so
`2^ntz(n) ≤ n` (`two_pow_ntz_le`), and its lowest set bit, `n ∧ (0 − n)` in
64 bits, is `2^ntz(n)` (`lowbit`): an implementation finds `L_{ntz(i)}`
without a branch on `i`.
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb (ntz)

/-- A positive `n` is `2^ntz(n)` times an odd number. -/
theorem ntz_spec (n : Nat) : 0 < n → ∃ u, n = 2 ^ ntz n * u ∧ u % 2 = 1 := by
  refine Nat.strongRecOn n ?_
  intro n ih h0
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨u, hu, hu2⟩ := ih (n / 2) (by omega) (by omega)
    refine ⟨u, ?_, hu2⟩
    rw [ntz_even h0 he, Nat.pow_succ, Nat.mul_comm (2 ^ ntz (n / 2)) 2, Nat.mul_assoc, ← hu]
    omega
  · exact ⟨n, by rw [ntz_odd ho]; simp, ho⟩

theorem two_pow_ntz_le {n : Nat} (h0 : 0 < n) : 2 ^ ntz n ≤ n := by
  obtain ⟨u, hu, hu2⟩ := ntz_spec n h0
  generalize ntz n = t at hu ⊢
  rw [hu]; exact Nat.le_mul_of_pos_right _ (by omega)

/-- An odd `u`'s lowest set bit is 1. -/
theorem and_neg_odd (u : BitVec 64) (h : u.getLsbD 0 = true) : u &&& (0#64 - u) = 1#64 := by
  have h1 : ~~~u &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
    rcases Nat.eq_zero_or_pos i with rfl | hp
    · simp [h]
    · simp [show i ≠ 0 by omega]
  rw [BitVec.zero_sub, BitVec.neg_eq_not_add, BitVec.add_eq_or_of_and_eq_zero _ _ h1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_one]
  rcases Nat.eq_zero_or_pos i with rfl | hp
  · simp [h]
  · simp [show i ≠ 0 by omega, hi]

theorem and_neg_shl (y : BitVec 64) (t : Nat) :
    (y <<< t) &&& (0#64 - (y <<< t)) = (y &&& (0#64 - y)) <<< t := by
  rw [BitVec.shiftLeft_and_distrib, BitVec.zero_sub, BitVec.zero_sub]
  simp only [BitVec.shiftLeft_eq_mul_twoPow, BitVec.neg_mul]

/-- The lowest set bit of a positive `n < 2^64`, `n ∧ (0 − n)`, is `2^ntz(n)`. -/
theorem lowbit {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& (0#64 - BitVec.ofNat 64 n) = BitVec.ofNat 64 (2 ^ ntz n) := by
  obtain ⟨u, hu, hu2⟩ := ntz_spec n h0
  generalize ntz n = t at hu ⊢
  have hu1 : 1 ≤ u := by omega
  have hp : 2 ^ t ≤ n := by rw [hu]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hun : u ≤ n := by rw [hu]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have e : BitVec.ofNat 64 n = BitVec.ofNat 64 u <<< t := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega),
      Nat.shiftLeft_eq, hu, Nat.mul_comm]
  have ho : (BitVec.ofNat 64 u).getLsbD 0 = true := by
    simp [BitVec.getLsbD_ofNat, Nat.testBit_zero, hu2]
  rw [e, and_neg_shl, and_neg_odd _ ho]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 1) (by decide), Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Ocb
