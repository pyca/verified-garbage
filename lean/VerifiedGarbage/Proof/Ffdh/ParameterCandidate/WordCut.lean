module

public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH parameter candidates: shaping and cutting the top word of a number of words

A number of `w` words whose top word is and'ed with `2^k − 1` is the number
mod `2^(64 (w − 1) + k)` (`wv_cut`); with the top word's bit `k − 1` and
the low word's bit 0 set too, it is the candidate of `64 (w − 1) + k` bits
(`wv_shape`). For any target whose words are 64 bits.
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen

theorem testBit_ofNat_pow_sub_one {k : Nat} (hk : k ≤ 64) (j : Nat) :
    (BitVec.ofNat 64 (2 ^ k - 1)).toNat.testBit j = decide (j < k) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; omega),
    Nat.testBit_two_pow_sub_one]

theorem testBit_ofNat_pow {k : Nat} (hk : k < 64) (j : Nat) :
    (BitVec.ofNat 64 (2 ^ k)).toNat.testBit j = decide (k = j) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk), Nat.testBit_two_pow]

/-- The top word and'ed with `2^k − 1`: the number cut to `64 (w − 1) + k` bits. -/
theorem wv_cut {m m' : Mem} {p : Addr} {d w k : Nat} (hw : 1 ≤ w) (hk : k ≤ 64)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ k - 1))
    (hlow : ∀ j, j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = wv m p d w % 2 ^ (64 * (w - 1) + k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi, testBit_wv m p d w i hi]
    by_cases hjt : i / 64 = w - 1
    · rw [hjt, htop, BitVec.toNat_and, Nat.testBit_and, testBit_ofNat_pow_sub_one hk]
      have e : decide (i % 64 < k) = decide (i < 64 * (w - 1) + k) := decide_eq_decide.mpr (by omega)
      rw [e, Bool.and_comm]
    · rw [hlow (i / 64) (by omega), decide_eq_true (show i < 64 * (w - 1) + k by omega), Bool.true_and]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp

/-- The top word cut to `k` bits with bit `k − 1` set, and the low bit set:
the candidate of `64 (w − 1) + k` bits. -/
theorem wv_shape {m m' : Mem} {p : Addr} {d w k : Nat} (hw : 2 ≤ w) (hk1 : 1 ≤ k) (hk : k ≤ 64)
    (h0 : word m' p d = word m p d ||| 1)
    (htop : word m' p (d + 8 * (w - 1)) =
      (word m p (d + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ k - 1)) ||| BitVec.ofNat 64 (2 ^ (k - 1)))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = Spec.Ffdh.candidateOf (64 * (w - 1) + k) (wv m p d w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold Spec.Ffdh.candidateOf
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi, testBit_wv m p d w i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or,
        show (1 : BitVec 64).toNat = 1 from rfl, show i % 64 = i by omega,
        decide_eq_true (show i < 64 * (w - 1) + k by omega), decide_eq_false (show ¬ 64 * (w - 1) + k - 1 = i by omega)]
      simp only [Bool.true_and, Bool.or_false]
    · have h1 := testBit_one_ne (show i ≠ 0 by omega)
      rw [h1, Bool.or_false]
      by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_and, Nat.testBit_and,
          testBit_ofNat_pow_sub_one hk, testBit_ofNat_pow (show k - 1 < 64 by omega)]
        have e1 : decide (i % 64 < k) = decide (i < 64 * (w - 1) + k) := decide_eq_decide.mpr (by omega)
        have e2 : decide (k - 1 = i % 64) = decide (64 * (w - 1) + k - 1 = i) := decide_eq_decide.mpr (by omega)
        rw [e1, e2, Bool.and_comm]
      · rw [hmid (i / 64) (by omega) (by omega), decide_eq_true (show i < 64 * (w - 1) + k by omega),
          decide_eq_false (show ¬ 64 * (w - 1) + k - 1 = i by omega)]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      testBit_one_ne (show i ≠ 0 by omega), decide_eq_false (show ¬ 64 * (w - 1) + k - 1 = i by omega),
      decide_eq_false (show ¬ i < 64 * (w - 1) + k by omega)]
    simp

end VG.Proof.Ffdh.ParameterCandidate
