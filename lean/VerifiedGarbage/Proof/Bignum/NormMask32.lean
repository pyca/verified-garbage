module

import VerifiedGarbage.Proof.Framework.Omega

/-!
# A 32-bit word's normalization by doublings under a mask

Target-independent (x86's and ARMv7's word steps): `clearMask a` is all ones
where `a`'s top bit is clear; doubling `T 2^i` and `2^i` under it takes them
to `T 2^min(i + 1, z)` and `2^min(i + 1, z)` for the leading zeros `z = lz T`
of `T ≠ 0` (`normStep_val`).
-/

@[expose] public section

namespace VG.Proof.Bignum.NormMask32

/-- The mask of a clear top bit. -/
def clearMask (a : BitVec 32) : BitVec 32 := (a >>> 31) - 1

/-- The leading zeros of a nonzero word. -/
def lz (T : Nat) : Nat := 31 - T.log2

/-- `T 2^i` for `i ≤ lz T` fits a word, with its top bit set exactly when `i = lz T`. -/
theorem shifted_bounds {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    T * 2 ^ i < 2 ^ 32 ∧ (T * 2 ^ i / 2 ^ 31 = if i = lz T then 1 else 0) := by
  have hL : T.log2 < 32 := (Nat.log2_lt (by omega)).mpr hT'
  have h1 := Nat.log2_self_le (n := T) (by omega)
  have h2 := Nat.lt_log2_self (n := T)
  unfold lz at hi ⊢
  have u : T * 2 ^ i < 2 ^ (T.log2 + 1 + i) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
  have l : 2 ^ (T.log2 + i) ≤ T * 2 ^ i := by rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  have p1 : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨Nat.lt_of_lt_of_le u p1, ?_⟩
  by_cases e : i = 31 - T.log2
  · simp only [e, ite_true]
    have a : 2 ^ (T.log2 + (31 - T.log2)) = 2 ^ 31 := congrArg _ (by omega)
    have b : 2 ^ (T.log2 + 1 + (31 - T.log2)) = 2 * 2 ^ 31 := by
      rw [show T.log2 + 1 + (31 - T.log2) = 31 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [e] at u l
    rw [Nat.div_eq_iff (by decide)]; omega
  · simp only [e, ite_false]
    have : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.div_eq_of_lt (by omega)

/-- A step of the doublings: `T 2^i` and `2^i` to `T 2^min(i + 1, z)` and `2^min(i + 1, z)`. -/
theorem normStep_val {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    BitVec.ofNat 32 (T * 2 ^ i) + (BitVec.ofNat 32 (T * 2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (T * 2 ^ min (i + 1) (lz T)) ∧
    BitVec.ofNat 32 (2 ^ i) + (BitVec.ofNat 32 (2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (2 ^ min (i + 1) (lz T)) := by
  obtain ⟨b1, b2⟩ := shifted_bounds hT hT' hi
  have hm : clearMask (BitVec.ofNat 32 (T * 2 ^ i)) = if i = lz T then 0 else BitVec.allOnes 32 := by
    unfold clearMask
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b1,
      Nat.shiftRight_eq_div_pow, b2]
    by_cases e : i = lz T <;> simp [e]
  rw [hm]
  by_cases e : i = lz T
  · simp only [e, ite_true, Nat.min_eq_right (Nat.le_succ _)]
    exact ⟨by simp, by simp⟩
  · simp only [e, ite_false, BitVec.and_allOnes, ← BitVec.ofNat_add]
    rw [Nat.min_eq_left (by omega), Nat.pow_succ]
    exact ⟨congrArg _ (by rw [← Nat.mul_assoc]; omega), congrArg _ (by omega)⟩

end VG.Proof.Bignum.NormMask32
