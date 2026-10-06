import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.Words

/-!
# A candidate for an RSA prime: arithmetic the implementations share

The witness from its random octets (`witness_eq`, `wv_le_one`); `|c − p|`
from a difference and its borrow (`absDiff_of`); and the bits a word
shifted left gives (`shift_step`).
-/

namespace VG.Proof.RsaKeyGen

open VG VG.Proof.Bignum

theorem and_m2_eq_zero (x : BitVec 64) : x &&& (BitVec.allOnes 64 - 1) = 0 ↔ x.toNat ≤ 1 := by
  have hmb : ∀ i < 64, 1 ≤ i → (BitVec.allOnes 64 - 1).getLsbD i = true := by decide
  constructor
  · intro h
    have : x.toNat < 2 ^ 1 := Nat.lt_pow_two_of_testBit _ fun i hi => by
      by_cases hi64 : i < 64
      · have := congrArg (fun y : BitVec 64 => y.getLsbD i) h
        simp only [BitVec.getLsbD_and, hmb i hi64 hi, Bool.and_true] at this
        rw [BitVec.testBit_toNat]; simpa using this
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    omega
  · intro h
    rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
    · rw [show x = 0#64 from BitVec.eq_of_toNat_eq h]; decide
    · rw [show x = 1#64 from BitVec.eq_of_toNat_eq h]; decide

/-- A number of `w ≥ 1` words is at most 1 iff its low word is and the others
are zero. -/
theorem wv_le_one {m : Mem} {p : Addr} {d w : Nat} (hw : 1 ≤ w) :
    wv m p d w ≤ 1 ↔ (word m p d &&& (BitVec.allOnes 64 - 1) = 0 ∧ ∀ i, 1 ≤ i → i < w → word m p (d + 8 * i) = 0) := by
  have e := wv_add m p d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at e
  have h1 : wv m p d 1 = (word m p d).toNat := by simp [wv]
  rw [e, h1, and_m2_eq_zero]
  have hz := wv_eq_zero_iff m p (d + 8 * 1) (w - 1)
  constructor
  · intro h
    have h2 : wv m p (d + 8 * 1) (w - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m p (d + 8 * 1) (w - 1)) with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ (64 * 1)) h0; simp at this; omega
    refine ⟨by omega, fun i hi hiw => ?_⟩
    have := hz.mp h2 (i - 1) (by omega)
    rwa [show d + 8 * 1 + 8 * (i - 1) = d + 8 * i by omega] at this
  · rintro ⟨h0, h⟩
    rw [hz.mpr fun q hq => by rw [show d + 8 * 1 + 8 * q = d + 8 * (q + 1) by omega]; exact h (q + 1) (by omega) (by omega)]
    omega

/-- The witness from `x < 2^(64 w)` for the odd `c` with `c − 1` of
`64 w` bits. -/
theorem witness_eq {c x w : Nat} (hc : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    (hx : x < 2 ^ (64 * w)) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if decide (2 ≤ x) && decide (x + (1 - x % 2) < c) then x else (x ||| 2) % 2 ^ (64 * w - 1),
        decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) := by
  have e : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = decide (2 ≤ x ∧ x < c - 1) := by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (by omega)
  rw [e]
  unfold Spec.RsaKeyGen.witness
  simp only [hb, Nat.mod_eq_of_lt hx]
  by_cases h : 2 ≤ x ∧ x < c - 1 <;> simp [h]

/-- `|c − p|` from the difference `D` and its borrow `b`. -/
theorem absDiff_of {D p c P : Nat} {b : Bool} (h : D + p = c + P * b.toNat) (hD : D < P) :
    (if b then P - D else D) = Spec.RsaKeyGen.absDiff c p := by
  unfold Spec.RsaKeyGen.absDiff
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
    Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> split <;> omega

/-- A word shifted left `i` bits, `y = (x mod 2^(k + 1)) 2^i` for `k + i = 63`,
and its next bit: what `add rdx, rdx` shifts out and leaves. -/
theorem shift_step (x k i : Nat) (hki : k + i = 63) :
    (x % 2 ^ (k + 1)) * 2 ^ i < 2 ^ 64 ∧
    (decide (2 ^ 64 ≤ (x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i)).toNat = x / 2 ^ k % 2 ∧
    ((x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 64 = (x % 2 ^ k) * 2 ^ (i + 1) ∧
    x / 2 ^ (k + 1) * 2 + x / 2 ^ k % 2 = x / 2 ^ k := by
  rw [Nat.mod_pow_succ]
  have hPQ : 2 ^ k * 2 ^ i = 2 ^ 63 := by rw [← Nat.pow_add, hki]
  have hb : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlow : x % 2 ^ k * 2 ^ i < 2 ^ 63 := by
    rw [← hPQ]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  have hexp : (x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2)) * 2 ^ i = x % 2 ^ k * 2 ^ i + 2 ^ 63 * (x / 2 ^ k % 2) := by
    rw [Nat.add_mul, ← hPQ, Nat.mul_right_comm (2 ^ k) _ (2 ^ i)]
  have h2i : x % 2 ^ k * 2 ^ (i + 1) = 2 * (x % 2 ^ k * 2 ^ i) := by
    rw [Nat.pow_succ]; rw [Nat.mul_comm 2, Nat.mul_assoc]
  have hdiv : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hexp, h2i, hdiv]
  have hd := Nat.div_add_mod (x / 2 ^ k) 2
  generalize x % 2 ^ k * 2 ^ i = M at hlow ⊢
  generalize x / 2 ^ k % 2 = b at hb hd ⊢
  refine ⟨by omega, ?_, by omega, by omega⟩
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

end VG.Proof.RsaKeyGen
