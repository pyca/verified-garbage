module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH parameter candidates: halving a number of words in place

Each word shifted right by one, with the next word's low bit shifted in at
the top, is the number halved (`wv_half`). For any target whose words are 64
bits.
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen

theorem wv_half {m m' : Mem} {p : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hlo : ∀ j, j + 1 < w →
      word m' p (d + 8 * j) = (word m p (d + 8 * j) >>> 1) ||| (word m p (d + 8 * (j + 1)) <<< 63))
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) >>> 1) :
    wv m' p d w = wv m p d w / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi]
    by_cases hj : i / 64 + 1 < w
    · rw [hlo _ hj, BitVec.testBit_toNat, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
        simp only [show decide (i % 64 < 63) = true from decide_eq_true hb, Bool.not_true, Bool.and_false,
          Bool.false_and, Bool.or_false]
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 + 1 by omega,
          show (i + 1) % 64 = 0 by omega, BitVec.testBit_toNat, BitVec.getLsbD_of_ge _ _ (by omega),
          show i % 64 - 63 = 0 by omega, Nat.mul_add, Nat.mul_one]
        simp only [show decide (i % 64 < 64) = true from decide_eq_true (by omega),
          show decide (i % 64 < 63) = false from decide_eq_false hb, Bool.not_false, Bool.true_and, Bool.false_or]
    · have he : i / 64 = w - 1 := by omega
      rw [he, htop, BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = w - 1 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
      · rw [BitVec.getLsbD_of_ge _ _ (by omega), Nat.testBit_lt_two_pow]
        exact Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega)))]

end VG.Proof.Ffdh.ParameterCandidate
