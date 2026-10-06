import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Spec.RsaKeyGen

/-!
# Bits of multiword numbers

`testBit_wv`: bit `i` of a number of words is bit `i mod 64` of its word
`i / 64`. So setting the low bit of the low word and the two top bits of the
top word makes the number `RsaKeyGen.candidate` (`wv_candidate`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem testBit_wv (m : Mem) (p : Addr) (d : Nat) : ∀ n i, i < 64 * n →
    (wv m p d n).testBit i = (word m p (d + 8 * (i / 64))).toNat.testBit (i % 64)
  | 0, i, h => by omega
  | n + 1, i, h => by
    rw [wv, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (wv_lt m p d n)]
    by_cases hi : i < 64 * n
    · simp only [hi, ↓reduceIte]; exact testBit_wv m p d n i hi
    · simp only [hi, ↓reduceIte]; rw [show i / 64 = n by omega, show i % 64 = i - 64 * n by omega]

theorem testBit_three_mul (k i : Nat) : (3 * 2 ^ k).testBit i = (decide (i = k) || decide (i = k + 1)) := by
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul, show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  omega

theorem testBit_one_ne {i : Nat} (h : i ≠ 0) : Nat.testBit 1 i = false := by
  rcases i with _ | i
  · exact absurd rfl h
  · rw [Nat.testBit_succ]; simp

/-- Setting the low bit and the two top bits of a number of `w ≥ 2` words:
the candidate of `64 w` bits from it. -/
theorem wv_candidate {m m' : Mem} {p : Addr} {d w : Nat} (hw : 2 ≤ w)
    (h0 : word m' p d = word m p d ||| 1)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = Spec.RsaKeyGen.candidate (64 * w) (wv m p d w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold Spec.RsaKeyGen.candidate
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow, testBit_three_mul]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi, testBit_wv m p d w i hi]
    simp only [hi, decide_true, Bool.true_and]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or,
        show (1 : BitVec 64).toNat = 1 from rfl, show i % 64 = i by omega,
        decide_eq_false (show ¬ i = 64 * w - 2 by omega), decide_eq_false (show ¬ i = 64 * w - 2 + 1 by omega)]
      simp
    · have h1 := testBit_one_ne (show i ≠ 0 by omega)
      rw [h1]
      by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 3 * 2 ^ 62 < 2 ^ 64 by decide), testBit_three_mul]
        have e1 : decide (i % 64 = 62) = decide (i = 64 * w - 2) := decide_eq_decide.mpr (by omega)
        have e2 : decide (i % 64 = 62 + 1) = decide (i = 64 * w - 2 + 1) := decide_eq_decide.mpr (by omega)
        rw [e1, e2]; simp
      · rw [hmid (i / 64) (by omega) (by omega), decide_eq_false (show ¬ i = 64 * w - 2 by omega),
          decide_eq_false (show ¬ i = 64 * w - 2 + 1 by omega)]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      testBit_one_ne (show i ≠ 0 by omega), decide_eq_false (show ¬ i = 64 * w - 2 by omega),
      decide_eq_false (show ¬ i = 64 * w - 2 + 1 by omega)]
    simp [hi]

end VG.Proof.RsaKeyGen.X86_64
