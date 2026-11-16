module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Two powers of one base with shared squarings: the arithmetic

Right to left, three bits of the exponent at a time: at digit `i` the base's
power `A = g^(8^i)` is multiplied into the bucket of the digit's value, so
bucket `d` holds `g^(bexp e k d)` after `k` digits, and the product of
`bucket_d^d` over the digits' values is `g^(e mod 8^k)`.

That product is taken by a running product from the last bucket down: `cy`
is the exponent of the product of the buckets so far, and `cx` of the
product of those products.
-/

@[expose] public section

namespace VG.Proof.Dsa.Shared

/-- The exponent of bucket `d` after `k` digits of `e`: the sum of `8^i`
over the digits `i < k` of `e` that are `d`. -/
def bexp (e : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, d => bexp e k d + if e / 8 ^ k % 8 = d then 8 ^ k else 0

theorem bexp_zero (e d : Nat) : bexp e 0 d = 0 := rfl

theorem bexp_succ (e k d : Nat) :
    bexp e (k + 1) d = bexp e k d + if e / 8 ^ k % 8 = d then 8 ^ k else 0 := rfl

/-- The digit's own bucket takes `8^k`. -/
theorem bexp_digit (e k : Nat) : bexp e (k + 1) (e / 8 ^ k % 8) = bexp e k (e / 8 ^ k % 8) + 8 ^ k := by
  rw [bexp_succ, ite_eq_left rfl]

/-- Every other bucket is as it was. -/
theorem bexp_other {e k d : Nat} (h : e / 8 ^ k % 8 ≠ d) : bexp e (k + 1) d = bexp e k d := by
  rw [bexp_succ, ite_eq_right h, Nat.add_zero]

/-- The buckets' weighted sum is the exponent's low digits. -/
theorem bexp_sum (e k : Nat) :
    bexp e k 1 + 2 * bexp e k 2 + 3 * bexp e k 3 + 4 * bexp e k 4 + 5 * bexp e k 5 + 6 * bexp e k 6 +
      7 * bexp e k 7 = e % 8 ^ k := by
  induction k with
  | zero => simp only [bexp_zero, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    have hd : e / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_pow_succ, ← ih]
    simp only [bexp_succ]
    generalize e / 8 ^ k % 8 = d at hd
    generalize (8 : Nat) ^ k = p
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, Nat.reduceEqDiff, ↓reduceIte] <;> omega

/-- Once the exponent's digits are exhausted, the weighted sum is the exponent. -/
theorem bexp_sum_all {e k : Nat} (h : e / 8 ^ k = 0) :
    bexp e k 1 + 2 * bexp e k 2 + 3 * bexp e k 3 + 4 * bexp e k 4 + 5 * bexp e k 5 + 6 * bexp e k 6 +
      7 * bexp e k 7 = e := by
  rw [bexp_sum, Nat.mod_eq_of_lt]
  exact (Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide))).mp h

/-- The exponent of the product of the buckets from 7 down to `7 - n`. -/
def cy (b : Nat → Nat) : Nat → Nat
  | 0 => b 7
  | n + 1 => cy b n + b (6 - n)

/-- The exponent of the product of those products. -/
def cx (b : Nat → Nat) : Nat → Nat
  | 0 => b 7
  | n + 1 => cx b n + cy b (n + 1)

theorem cx_six (b : Nat → Nat) :
    cx b 6 = b 1 + 2 * b 2 + 3 * b 3 + 4 * b 4 + 5 * b 5 + 6 * b 6 + 7 * b 7 := by
  simp only [cx, cy, Nat.reduceSub]
  omega

/-- A digit of a value whose low bytes are `v`: `v`'s, while the digit lies
within them. -/
theorem digit_low {a v n i : Nat} (hi : 3 * i + 3 ≤ 8 * n) :
    (256 ^ n * a + v) / 8 ^ i % 8 = v / 8 ^ i % 8 := by
  have h256 : (256 : Nat) ^ n = 8 ^ (i + 1) * 2 ^ (8 * n - 3 * (i + 1)) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul, ← Nat.pow_mul,
      ← Nat.pow_add]
    congr 1
    omega
  rw [h256, Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_add_div (Nat.pow_pos (by decide)),
    Nat.mul_add_mod]

/-! ## The exponent's bytes, three at a time from the end -/

open VG.Proof.Bignum (pre pre_succ pre_zero)

/-- The digits in the group of bytes below index `r`: eight for three
bytes, and six or three for the last two bytes or one. -/
def gcount (r : Nat) : Nat := if 3 ≤ r then 8 else if 2 ≤ r then 6 else 3

/-- The value of the up to three bytes below index `r`. -/
def gval (bs : List Byte) (r : Nat) : Nat :=
  (bs[r - 1]?.getD 0).toNat + (if 2 ≤ r then 256 * (bs[r - 2]?.getD 0).toNat else 0) +
    (if 3 ≤ r then 65536 * (bs[r - 3]?.getD 0).toNat else 0)

theorem gcount_pos (r : Nat) : 1 ≤ gcount r := by
  unfold gcount; split
  · decide
  · split <;> decide

theorem gcount_le (r : Nat) : gcount r ≤ 8 := by
  unfold gcount; split
  · decide
  · split <;> decide

theorem gval_lt (bs : List Byte) (r : Nat) : gval bs r < 2 ^ 24 := by
  unfold gval
  have h1 := (bs[r - 1]?.getD 0).isLt
  have h2 := (bs[r - 2]?.getD 0).isLt
  have h3 := (bs[r - 3]?.getD 0).isLt
  split <;> split <;> omega

theorem getD_getElem (bs : List Byte) {i : Nat} (hi : i < bs.length) : bs[i]?.getD 0 = bs[i] := by
  rw [List.getElem?_eq_getElem hi]; rfl

/-- The group's value and count as the code computes them: one byte left, -/
theorem gval_one (bs : List Byte) {r : Nat} (hr : r = 1) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat ∧ gcount r = 3 := by
  subst hr
  simp only [gval, gcount, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero,
    getD_getElem bs (show 0 < bs.length by omega), and_self]

/-- two, -/
theorem gval_two (bs : List Byte) {r : Nat} (hr : r = 2) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat + 2 ^ 8 * (bs[r - 1 - 1]'(by omega)).toNat ∧ gcount r = 6 := by
  subst hr
  simp only [gval, gcount, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, Nat.le_refl,
    getD_getElem bs (show 0 < bs.length by omega), getD_getElem bs (show 1 < bs.length by omega),
    Nat.reducePow, and_self]

/-- or three and more. -/
theorem gval_three (bs : List Byte) {r : Nat} (hr : 3 ≤ r) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat + 2 ^ 8 * (bs[r - 1 - 1]'(by omega)).toNat +
      2 ^ 16 * (bs[r - 1 - 1 - 1]'(by omega)).toNat ∧ gcount r = 8 := by
  have e2 : r - 1 - 1 = r - 2 := by omega
  have e3 : r - 2 - 1 = r - 3 := by omega
  simp only [gval, gcount, hr, show 2 ≤ r by omega, ↓reduceIte, getD_getElem bs (show r - 1 < bs.length by omega),
    getD_getElem bs (show r - 2 < bs.length by omega), getD_getElem bs (show r - 3 < bs.length by omega),
    Nat.reducePow, e2, e3, and_self]

/-- The bytes below `r` are those below `r - 3`, and the group's. -/
theorem pre_group (bs : List Byte) {r : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) :
    pre bs r = 256 ^ min 3 r * pre bs (r - 3) + gval bs r ∧ gval bs r < 256 ^ min 3 r := by
  have g (i : Nat) (hi : i < bs.length) : (bs[i]?.getD 0) = bs[i] := by
    rw [List.getElem?_eq_getElem hi]; rfl
  unfold gval
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
  · have h1 : pre bs 1 = (bs[0]'(by omega)).toNat := by
      simpa only [Nat.zero_add, Nat.mul_zero, pre_zero] using pre_succ bs (i := 0) (by omega)
    have b1 := (bs[0]'(by omega)).isLt
    simp only [Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, pre_zero, Nat.mul_zero, Nat.zero_add,
      g 0 (by omega), show min 3 1 = 1 by decide, Nat.pow_one]
    omega
  · have h1 : pre bs 1 = (bs[0]'(by omega)).toNat := by
      simpa only [Nat.zero_add, Nat.mul_zero, pre_zero] using pre_succ bs (i := 0) (by omega)
    have h2 : pre bs 2 = 256 * pre bs 1 + (bs[1]'(by omega)).toNat := pre_succ bs (i := 1) (by omega)
    have b1 := (bs[0]'(by omega)).isLt
    have b2 := (bs[1]'(by omega)).isLt
    simp only [Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, pre_zero, Nat.mul_zero, Nat.zero_add,
      g 0 (by omega), g 1 (by omega), show min 3 2 = 2 by decide, Nat.le_refl]
    omega
  · have h1 := pre_succ bs (i := r - 3) (by omega)
    have h2 := pre_succ bs (i := r - 2) (by omega)
    have h3' := pre_succ bs (i := r - 1) (by omega)
    have b1 := (bs[r - 3]'(by omega)).isLt
    have b2 := (bs[r - 2]'(by omega)).isLt
    have b3 := (bs[r - 1]'(by omega)).isLt
    rw [show r - 3 + 1 = r - 2 by omega] at h1
    rw [show r - 2 + 1 = r - 1 by omega] at h2
    rw [show r - 1 + 1 = r by omega] at h3'
    simp only [h3, show 2 ≤ r by omega, ↓reduceIte, g (r - 1) (by omega), g (r - 2) (by omega),
      g (r - 3) (by omega), Nat.min_eq_left h3]
    omega

/-- The group's digits are the exponent's next ones. -/
theorem group_digit (bs : List Byte) {r i : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) (hi : i < gcount r) :
    pre bs r / 8 ^ i % 8 = gval bs r / 8 ^ i % 8 := by
  obtain ⟨h, -⟩ := pre_group bs hr hrl
  rw [h]
  by_cases h3 : 3 ≤ r
  · rw [Nat.min_eq_left h3]
    exact digit_low (by unfold gcount at hi; simp only [h3, ↓reduceIte] at hi; omega)
  · rw [show r - 3 = 0 by omega, pre_zero, Nat.mul_zero, Nat.zero_add]

/-- After the group's digits, the bytes below `r - 3` are left. -/
theorem group_rest (bs : List Byte) {r : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) :
    pre bs r / 8 ^ gcount r = pre bs (r - 3) := by
  obtain ⟨h, hlt⟩ := pre_group bs hr hrl
  rw [h]
  unfold gcount
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
  · simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.reduceSub, pre_zero, Nat.mul_zero, Nat.zero_add] at hlt ⊢
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))
  · simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.reduceSub, pre_zero, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
      at hlt ⊢
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))
  · rw [Nat.min_eq_left h3] at hlt ⊢
    simp only [h3, ↓reduceIte]
    rw [show (256 : Nat) ^ 3 = 8 ^ 8 by decide] at hlt ⊢
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hlt, Nat.add_zero]

end VG.Proof.Dsa.Shared
