module
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Halving a multiword number

`wv_half`: words `(s_i >> 1) | (s_(i+1) << 63)` below the top one and
`s_(n−1) >> 1` at the top are the number halved.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG VG.Proof.Bignum

theorem testBit_half_word (a b : BitVec 64) {q : Nat} (hq : q < 64) :
    ((a >>> 1) ||| (b <<< 63)).toNat.testBit q =
      if q < 63 then a.toNat.testBit (q + 1) else b.toNat.testBit 0 := by
  rw [BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, Nat.pow_one,
    show a.toNat / 2 = a.toNat / 2 ^ 1 from rfl, Nat.testBit_div_two_pow]
  by_cases h : q < 63
  · simp only [h, ↓reduceIte, hq, decide_true, Bool.true_and, show ¬ 63 ≤ q by omega, decide_false,
      Bool.false_and, Bool.or_false]
  · have : q = 63 := by omega
    subst this
    have h64 : a.toNat.testBit 64 = false := Nat.testBit_lt_two_pow a.isLt
    simp [h64]

theorem testBit_top_word (a : BitVec 64) {q : Nat} (hq : q < 64) :
    (a >>> 1).toNat.testBit q = if q < 63 then a.toNat.testBit (q + 1) else false := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show a.toNat / 2 ^ 1 = a.toNat / 2 ^ 1 from rfl,
    Nat.testBit_div_two_pow]
  by_cases h : q < 63
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Words `(s_i >> 1) | (s_(i+1) << 63)`, and `s_(n−1) >> 1` at the top: the
number halved. -/
theorem wv_half {m m' : Mem} {p p' : Addr} {d d' n : Nat} (hn : 1 ≤ n)
    (hlo : ∀ i, i + 1 < n → word m' p' (d' + 8 * i) =
      (word m p (d + 8 * i) >>> 1) ||| (word m p (d + 8 * (i + 1)) <<< 63))
    (htop : word m' p' (d' + 8 * (n - 1)) = word m p (d + 8 * (n - 1)) >>> 1) :
    wv m' p' d' n = wv m p d n / 2 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [show wv m p d n / 2 = wv m p d n / 2 ^ 1 from rfl, Nat.testBit_div_two_pow]
  by_cases hk : k < 64 * n
  · rw [testBit_wv m' p' d' n k hk]
    have hq : k % 64 < 64 := Nat.mod_lt _ (by decide)
    by_cases hi : k / 64 + 1 < n
    · rw [hlo (k / 64) hi, testBit_half_word _ _ hq, testBit_wv m p d n (k + 1) (by omega)]
      by_cases h63 : k % 64 < 63
      · simp only [h63, ↓reduceIte]
        rw [show (k + 1) / 64 = k / 64 by omega, show (k + 1) % 64 = k % 64 + 1 by omega]
      · simp only [h63, ↓reduceIte]
        rw [show (k + 1) / 64 = k / 64 + 1 by omega, show (k + 1) % 64 = 0 by omega]
    · have hkn : k / 64 = n - 1 := by omega
      rw [hkn, htop, testBit_top_word _ hq]
      by_cases h63 : k % 64 < 63
      · simp only [h63, ↓reduceIte]
        rw [testBit_wv m p d n (k + 1) (by omega), show (k + 1) / 64 = n - 1 by omega,
          show (k + 1) % 64 = k % 64 + 1 by omega]
      · simp only [h63, ↓reduceIte]
        exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d n)
          (Nat.pow_le_pow_right (by decide) (by omega)))).symm
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p' d' n) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d n) (Nat.pow_le_pow_right (by decide) (by omega)))]

end VG.Proof.RsaKeyGen
