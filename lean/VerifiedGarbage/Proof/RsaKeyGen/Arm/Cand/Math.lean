module

public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the bits the code sets and clears

The candidate's two top bits set by or'ing its top word with `0xC0000000`
(`topBits_val`), and its low bit by `orOne` (`candidate_eq`); a witness's
bit 1 set (`or_two_split`) and its top bit cleared by shifting its top word
(`clrTop_val`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand

/-- Or'ing a number below `2^(k + 2)` with `3 · 2^k`. -/
theorem or_three {x k : Nat} (hx : x < 2 ^ (k + 2)) : x ||| 3 * 2 ^ k = x % 2 ^ k + 3 * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, show x % 2 ^ k + 3 * 2 ^ k = 2 ^ k * 3 + x % 2 ^ k by rw [Nat.add_comm, Nat.mul_comm],
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos k)), Nat.mul_comm 3, Nat.testBit_two_pow_mul,
    Nat.testBit_mod_two_pow]
  by_cases h : i < k
  · simp only [h, decide_true, Bool.true_and, ↓reduceIte]
    have : ¬ k ≤ i := by omega
    simp [this]
  · simp only [h, ↓reduceIte]
    have hk : k ≤ i := by omega
    simp only [hk, decide_true, Bool.true_and]
    rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    by_cases h2 : i - k < 2
    · simp [h2]
    · simp only [h2, decide_false, Bool.or_false]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2) (by decide)
        (show k + 2 ≤ i by omega)))

/-- `candidate`, for a number of the candidate's bits, as the code sets the
bits: the two top bits, then the low bit. -/
theorem candidate_eq {b x : Nat} (hb : 2 ≤ b) (hx : x < 2 ^ b) :
    Spec.RsaKeyGen.candidate b x = 2 * ((x % 2 ^ (b - 2) + 3 * 2 ^ (b - 2)) / 2) + 1 := by
  unfold Spec.RsaKeyGen.candidate
  rw [Nat.mod_eq_of_lt hx, or_three (by rwa [show b - 2 + 2 = b by omega]), VG.Proof.Rsa.Arm.Keys.or_one]

theorem bv_or_top (v : BitVec 32) : (v ||| 0xC0000000#32).toNat = v.toNat % 2 ^ 30 + 3 * 2 ^ 30 := by
  rw [BitVec.toNat_or, show (0xC0000000#32).toNat = 3 * 2 ^ 30 from rfl, or_three v.isLt]

/-- The candidate's top word, word `i`, or'ed with `0xC0000000`. -/
theorem topBits_val {x i : Nat} (hx : x < 2 ^ (32 * i + 32)) :
    x % 2 ^ (32 * i) + 2 ^ (32 * i) * (BitVec.ofNat 32 (x / 2 ^ (32 * i) % 2 ^ 32) ||| 0xC0000000#32).toNat +
      2 ^ (32 * (i + 1)) * (x / 2 ^ (32 * (i + 1))) = x % 2 ^ (32 * i + 30) + 3 * 2 ^ (32 * i + 30) := by
  have e : x / 2 ^ (32 * (i + 1)) = 0 := Nat.div_eq_of_lt (by rwa [Nat.mul_succ])
  rw [e, Nat.mul_zero, Nat.add_zero, bv_or_top, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mul_add, ← Nat.add_assoc, Nat.pow_add, Nat.mod_mul]
  rw [Nat.mul_left_comm]

/-- A word shifted left one bit and back: its top bit cleared. -/
theorem bv_clr_top (v : BitVec 32) : ((v <<< 1) >>> 1).toNat = v.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  rw [show (2 : Nat) ^ 32 = 2 ^ 31 * 2 from rfl, Nat.pow_one, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

/-- The top word, word `i`, of a number of `i + 1` words with its top bit cleared. -/
theorem clrTop_val {x i : Nat} (hx : x < 2 ^ (32 * i + 32)) :
    x % 2 ^ (32 * i) + 2 ^ (32 * i) * ((BitVec.ofNat 32 (x / 2 ^ (32 * i) % 2 ^ 32) <<< 1) >>> 1).toNat +
      2 ^ (32 * (i + 1)) * (x / 2 ^ (32 * (i + 1))) = x % 2 ^ (32 * i + 31) := by
  have e : x / 2 ^ (32 * (i + 1)) = 0 := Nat.div_eq_of_lt (by rwa [Nat.mul_succ])
  rw [e, Nat.mul_zero, Nat.add_zero, bv_clr_top, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.pow_add, Nat.mod_mul]

/-- Or'ing with a number below `2^32` changes only the low word. -/
theorem or_low {x b : Nat} (hb : b < 2 ^ 32) : x ||| b = (x % 2 ^ 32 ||| b) + 2 ^ 32 * (x / 2 ^ 32) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hl : x % 2 ^ 32 ||| b < 2 ^ 32 := Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) hb
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases h : i < 32
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.or_false, Nat.sub_add_cancel (by omega)]

end VG.Proof.RsaKeyGen.Arm.Cand
