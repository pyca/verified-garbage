module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A witness's bits in 64-bit words

The word updates that make a draw of whole words a witness
(`Spec.RsaKeyGen.witness`), for a number of `n` words whose top `b` bits
(`1 ≤ b ≤ 64`) are in its word `t`:

* `wv_cut`: the top word and'ed with `2^b − 1` cuts the number to its low
  `64 t + b` bits;
* `wv_or_one`: the low word or'ed with 1 is the number or'ed with 1;
* `wv_fallback`: the low word or'ed with 2 and the top word and'ed with
  `2^(b−1) − 1` (for `t > 0`) is the fallback, `(x | 2) mod 2^(64 t + b − 1)`;
* `wv_lt_two_iff`: the number is below 2 exactly when its low word is and
  the others are zero.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG VG.Proof.Bignum

theorem testBit_and_mask {x : BitVec 64} {b : Nat} (i : Nat) (hb : b ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ b - 1)).toNat.testBit i = (x.toNat.testBit i && decide (i < b)) := by
  rw [BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ b - 1 < 2 ^ 64 from by have := Nat.pow_le_pow_right (n := 2) (by decide) hb; omega),
    Nat.testBit_two_pow_sub_one]

theorem wv_bits_high {m : Mem} {p : Addr} {d n i : Nat} (hi : 64 * n ≤ i) : (wv m p d n).testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d n) (Nat.pow_le_pow_right (by decide) hi))

/-- The top word and'ed with `2^b − 1`: the number's low `64 t + b` bits. -/
theorem wv_cut {m m' : Mem} {p : Addr} {d n t b : Nat} (hb : b ≤ 64)
    (top : word m' p (d + 8 * t) = word m p (d + 8 * t) &&& BitVec.ofNat 64 (2 ^ b - 1))
    (rest : ∀ j < n, j ≠ t → word m' p (d + 8 * j) = word m p (d + 8 * j))
    (hV : wv m p d n < 2 ^ (64 * (t + 1))) :
    wv m' p d n = wv m p d n % 2 ^ (64 * t + b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 64 * n
  · rw [testBit_wv m' p d n i hi, testBit_wv m p d n i hi]
    by_cases hj : i / 64 = t
    · rw [hj, top, testBit_and_mask _ hb, Bool.and_comm]
      congr 1
      exact decide_eq_decide.mpr (by omega)
    · rw [rest (i / 64) (by omega) hj]
      by_cases hlt : i / 64 < t
      · simp only [show i < 64 * t + b by omega, decide_true, Bool.true_and]
      · have hz : (wv m p d n).testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hV (Nat.pow_le_pow_right (by decide) (by omega)))
        rw [testBit_wv m p d n i hi] at hz
        rw [hz, Bool.and_false]
  · rw [wv_bits_high (by omega), wv_bits_high (by omega), Bool.and_false]

/-- The low word or'ed with 1, of a copy at `d` of the number at `d'`. -/
theorem wv_or_one {m m' : Mem} {p : Addr} {d d' n : Nat} (hn : 1 ≤ n)
    (low : word m' p d = word m p d' ||| 1#64)
    (rest : ∀ j < n, j ≠ 0 → word m' p (d + 8 * j) = word m p (d' + 8 * j)) :
    wv m' p d n = wv m p d' n ||| 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 64 * n
  · rw [testBit_wv m' p d n i hi, testBit_wv m p d' n i hi]
    by_cases hj : i / 64 = 0
    · rw [hj, Nat.mul_zero, Nat.add_zero, Nat.add_zero, low, BitVec.toNat_or, Nat.testBit_or,
        show (1#64 : BitVec 64).toNat = 1 from rfl, show i % 64 = i by omega]
    · rw [rest (i / 64) (by omega) hj, testBit_one_ne (show i ≠ 0 by omega), Bool.or_false]
  · rw [wv_bits_high (by omega), wv_bits_high (by omega), testBit_one_ne (show i ≠ 0 by omega)]
    rfl

/-- The fallback: the low word or'ed with 2 and the top word (`t > 0`)
and'ed with `2^(b−1) − 1`. -/
theorem wv_fallback {m m' : Mem} {p : Addr} {d n t b : Nat} (ht0 : 0 < t) (ht : t < n) (hb1 : 1 ≤ b)
    (hb : b ≤ 64)
    (low : word m' p d = word m p d ||| 2#64)
    (top : word m' p (d + 8 * t) = word m p (d + 8 * t) &&& BitVec.ofNat 64 (2 ^ (b - 1) - 1))
    (rest : ∀ j < n, j ≠ 0 → j ≠ t → word m' p (d + 8 * j) = word m p (d + 8 * j))
    (hV : wv m p d n < 2 ^ (64 * t + b)) :
    wv m' p d n = (wv m p d n ||| 2) % 2 ^ (64 * t + b - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, testBit_two]
  by_cases hi : i < 64 * n
  · rw [testBit_wv m' p d n i hi, testBit_wv m p d n i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, low, BitVec.toNat_or, Nat.testBit_or,
        show (2#64 : BitVec 64).toNat = 2 from rfl, testBit_two, show i % 64 = i by omega]
      simp only [show i < 64 * t + b - 1 by omega, decide_true, Bool.true_and]
    · by_cases hjt : i / 64 = t
      · rw [hjt, top, testBit_and_mask _ (by omega), decide_eq_false (by omega : i ≠ 1),
          Bool.or_false, Bool.and_comm]
        congr 1
        exact decide_eq_decide.mpr (by omega)
      · rw [rest (i / 64) (by omega) hj0 hjt, decide_eq_false (by omega : i ≠ 1), Bool.or_false]
        by_cases hlt : i / 64 < t
        · simp only [show i < 64 * t + b - 1 by omega, decide_true, Bool.true_and]
        · have hz : (wv m p d n).testBit i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hV (Nat.pow_le_pow_right (by decide) (by omega)))
          rw [testBit_wv m p d n i hi] at hz
          rw [hz, Bool.and_false]
  · rw [wv_bits_high (by omega), wv_bits_high (by omega), decide_eq_false (by omega : i ≠ 1), Bool.or_false,
      Bool.and_false]

/-- For odd `c`, `(x | 1) < c` exactly when `x < c − 1`. -/
theorem or_one_lt_iff {x c : Nat} (hc : c % 2 = 1) : x ||| 1 < c ↔ x < c - 1 := by
  have e : x ||| 1 = 2 * (x / 2) + 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    rcases i with _ | i
    · simp [Nat.testBit_zero]
    · rw [testBit_one_ne (by omega), Bool.or_false, Nat.testBit_succ, Nat.testBit_succ,
        show (2 * (x / 2) + 1) / 2 = x / 2 by omega]
  rw [e]
  omega

/-- Below 2 exactly when the low word is and the others are zero. -/
theorem wv_lt_two_iff (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n < 2 ↔ (word m p d).toNat < 2 ∧ ∀ j, 1 ≤ j → j < n → word m p (d + 8 * j) = 0 := by
  have e := wv_add m p d 1 (n - 1)
  rw [show 1 + (n - 1) = n by omega] at e
  have e1 : wv m p d 1 = (word m p d).toNat := by simp [wv]
  rw [e, e1]
  have hz := wv_eq_zero_iff m p (d + 8 * 1) (n - 1)
  constructor
  · intro h
    have h0 : wv m p (d + 8 * 1) (n - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m p (d + 8 * 1) (n - 1)) with h0 | h0
      · exact h0
      · have : 2 ^ (64 * 1) * wv m p (d + 8 * 1) (n - 1) ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ h0
        omega
    refine ⟨by omega, fun j hj hjn => ?_⟩
    have := hz.mp h0 (j - 1) (by omega)
    rwa [show d + 8 * 1 + 8 * (j - 1) = d + 8 * j by omega] at this
  · rintro ⟨h0, hr⟩
    have : wv m p (d + 8 * 1) (n - 1) = 0 := hz.mpr fun q hq => by
      rw [show d + 8 * 1 + 8 * q = d + 8 * (q + 1) by omega]; exact hr (q + 1) (by omega) (by omega)
    rw [this, Nat.mul_zero, Nat.add_zero]; exact h0

end VG.Proof.RsaKeyGen
