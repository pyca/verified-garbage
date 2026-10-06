import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.GcmSiv.Words

/-!
# AES-GCM-SIV: POLYVAL is GHASH

Untrusted: everything here is checked by Lean. RFC 8452's POLYVAL computes
in `GF(2)[y] / (y¹²⁸ + y¹²⁷ + y¹²⁶ + y¹²¹ + 1)` with the coefficient of `yⁱ`
in bit `i` of a block (`getLsbD i`), and GCM's GHASH in
`GF(2)[x] / (x¹²⁸ + x⁷ + x² + x + 1)` with it in bit `i` from the left
(`getMsbD i`, `Proof.Gcm.Poly`). The two polynomials are reciprocal, so
`y ↦ x⁻¹` maps one field onto the other, and on the same 128 bits it is
`φ` (the class of a block in GHASH's field) up to a power of `x`. Then
`dot(a, b) = a · b · y⁻¹²⁸` is GHASH's product of `a` and `b · x`
(`dot_eq`), and POLYVAL with `H` is GHASH with `H · x` (`polyvalFrom_eq`),
RFC 8452's Appendix A: with blocks read in the other byte order (`ofBytes_eq`,
`toBytes_eq`), so that the bits are the same. So the tag input is the one
computed with GHASH (`tagInput_eq_tagInputG`).
-/

namespace VG.Proof.GcmSiv.Polyval

open Polynomial VG.Proof.Gcm.Poly

/-- `x⁻¹`: `x · (x¹²⁷ + x⁶ + x + 1) = x¹²⁸ + x⁷ + x² + x = 1`. -/
noncomputable def xi : Q := x ^ 127 + x ^ 6 + x + 1

theorem x_xi : x * xi = 1 := by
  unfold xi; linear_combination x128 + (x ^ 7 + x ^ 2 + x) * two_Q

theorem cancel_pow {u v : Q} (k : Nat) (h : x ^ k * u = x ^ k * v) : u = v := by
  have e : xi ^ k * x ^ k = 1 := by rw [← mul_pow, mul_comm, x_xi, one_pow]
  calc u = xi ^ k * (x ^ k * u) := by rw [← mul_assoc, e, one_mul]
    _ = xi ^ k * (x ^ k * v) := by rw [h]
    _ = v := by rw [← mul_assoc, e, one_mul]

/-- The polynomial of a block whose set bits (from the left) are `S`. -/
theorem gp_of_bits (v : BitVec 128) (S : Finset ℕ) (hS : ∀ d ∈ S, d < 128)
    (h : ∀ d < 128, v.getMsbD d = decide (d ∈ S)) : gp v = ∑ d ∈ S, X ^ d := by
  ext k
  rw [coeff_gp, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hk : k < 128
  · rw [h k hk]; by_cases hm : k ∈ S <;> simp [hm, bit]
  · have e : v.getMsbD k = false := by
      simp only [BitVec.getMsbD, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
    have hm : k ∉ S := fun hm => hk (hS k hm)
    simp [e, hm, bit]

theorem φ_poly : φ Spec.GcmSiv.poly = 1 + x + x ^ 6 + x ^ 127 := by
  rw [φ, gp_of_bits Spec.GcmSiv.poly {0, 1, 6, 127} (by decide) (by decide +kernel)]
  simp [Finset.sum_insert]
  ring

theorem φ_xInv128 : φ Spec.GcmSiv.xInv128 = 1 + x ^ 3 + x ^ 6 + x ^ 13 + x ^ 127 := by
  rw [φ, gp_of_bits Spec.GcmSiv.xInv128 {0, 3, 6, 13, 127} (by decide) (by decide +kernel)]
  simp [Finset.sum_insert]
  ring

theorem x255 : x ^ 255 = 1 + x ^ 3 + x ^ 6 + x ^ 13 + x ^ 127 := by
  linear_combination (x ^ 127 + x ^ 6 + x + 1) * x128 + (x ^ 8 + x ^ 7 + x ^ 2 + x) * two_Q

/-- A shift to the left by one bit is a shift towards `x⁰` in GHASH's
order: `x · gp (a <<< 1) + a₀ = gp a`, where `a₀` is the leftmost bit. -/
theorem gp_shl1 (a : BitVec 128) :
    X * gp (a <<< 1) + (if a.getMsbD 0 then 1 else 0) = gp a := by
  ext d
  rw [coeff_add, coeff_gp]
  rcases d with _ | d
  · rw [coeff_X_mul_zero, zero_add]
    split_ifs with h <;> simp [h, bit]
  · rw [coeff_X_mul, coeff_gp]
    have e : (a <<< 1).getMsbD d = a.getMsbD (d + 1) := by
      simp only [BitVec.getMsbD, BitVec.getLsbD_shiftLeft]
      by_cases h : d + 1 < 128
      · simp only [show d < 128 by omega, h, decide_true, Bool.true_and]
        rw [show 128 - 1 - d - 1 = 128 - 1 - (d + 1) by omega]
        simp [show ¬ (128 - 1 - d < 1) by omega]; omega
      · by_cases h' : d < 128
        · simp only [h', h, decide_true, decide_false, Bool.true_and, Bool.false_and]
          simp only [show 128 - 1 - d < 1 by omega, decide_true, Bool.not_true, Bool.false_and,
            Bool.and_false]
        · simp only [h', h, decide_false, Bool.false_and]
    rw [e]
    split_ifs <;> simp [coeff_one]

theorem φ_shl1 (a : BitVec 128) : x * φ (a <<< 1) + (if a.getLsbD 127 then 1 else 0) = φ a := by
  have h := congrArg (AdjoinRoot.mk g) (gp_shl1 a)
  have e : a.getMsbD 0 = a.getLsbD 127 := by simp [BitVec.getMsbD]
  rw [e] at h
  simp only [map_add, map_mul, AdjoinRoot.mk_X] at h
  rw [φ, φ, ← h]
  split_ifs <;> simp

/-- POLYVAL's `mulX` (the product with `y`) is division by `x`. -/
theorem φ_mulX (a : BitVec 128) : x * φ (Spec.GcmSiv.mulX a) = φ a := by
  have h := φ_shl1 a
  unfold Spec.GcmSiv.mulX
  split_ifs with ha
  · rw [φ_xor, φ_poly]
    simp only [ha, ↓reduceIte] at h
    linear_combination h + x128 + (x ^ 7 + x ^ 2 + x) * two_Q
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, add_zero] at h
    exact h

/-- The first `k` steps of POLYVAL's product of `a` and `b`. -/
def mulSteps (a b : Spec.GcmSiv.Elem) (k : Nat) : Spec.GcmSiv.Elem :=
  (List.range k).foldl
    (fun z i => if a.getLsbD (127 - i) then Spec.GcmSiv.mulX z ^^^ b else Spec.GcmSiv.mulX z) 0

theorem mulSteps_φ (a b : Spec.GcmSiv.Elem) (k : Nat) :
    x ^ k * φ (mulSteps a b k) =
      φ b * ∑ i ∈ Finset.range k, (if a.getLsbD (127 - i) then x ^ (i + 1) else 0) := by
  induction k with
  | zero => simp [mulSteps, φ_zero']
  | succ k ih =>
    have e : mulSteps a b (k + 1) =
        if a.getLsbD (127 - k) then Spec.GcmSiv.mulX (mulSteps a b k) ^^^ b
        else Spec.GcmSiv.mulX (mulSteps a b k) := by
      simp only [mulSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ, mul_add, ← ih]
    have hm := φ_mulX (mulSteps a b k)
    split_ifs
    · rw [φ_xor, mul_add, ← hm]; ring
    · rw [← hm]; ring

/-- POLYVAL's product: `x¹²⁸ · φ (a · b) = x · φ a · φ b`. -/
theorem φ_mul (a b : Spec.GcmSiv.Elem) : x ^ 128 * φ (Spec.GcmSiv.mul a b) = x * φ a * φ b := by
  have h := mulSteps_φ a b 128
  rw [show Spec.GcmSiv.mul a b = mulSteps a b 128 from rfl, h, φ_eq a, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < 128 := Finset.mem_range.mp hi
  have e : a.getMsbD i = a.getLsbD (127 - i) := by
    simp only [BitVec.getMsbD, hi, decide_true, Bool.true_and]
  rw [e]
  split_ifs <;> ring

/-- `dot(a, b)` is GHASH's product of `a` and `b · x`. -/
theorem φ_dot (a b : Spec.GcmSiv.Elem) : φ (Spec.GcmSiv.dot a b) = x * φ a * φ b := by
  refine cancel_pow 128 ?_
  have h₁ := φ_mul (Spec.GcmSiv.mul a b) Spec.GcmSiv.xInv128
  have h₂ := φ_mul a b
  rw [show Spec.GcmSiv.dot a b = Spec.GcmSiv.mul (Spec.GcmSiv.mul a b) Spec.GcmSiv.xInv128 from rfl, h₁,
    φ_xInv128, ← x255]
  linear_combination (x ^ 128) * h₂

theorem dot_eq (a b : Spec.GcmSiv.Elem) : Spec.GcmSiv.dot a b = Spec.Gcm.mul a (mulXG b) := by
  refine φ_inj ?_
  rw [φ_dot, VG.Proof.Gcm.Poly.φ_mul, mulXG, φ_shr1]
  ring

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`, on the same
bits. -/
theorem polyvalFrom_eq (h s : Spec.GcmSiv.Elem) (xs : List Spec.GcmSiv.Elem) :
    Spec.GcmSiv.polyvalFrom h s xs = Spec.Gcm.ghashFrom (mulXG h) s xs := by
  induction xs generalizing s with
  | nil => simp only [Spec.GcmSiv.polyvalFrom, Spec.Gcm.ghashFrom, List.foldl_nil]
  | cons y ys ih =>
    show Spec.GcmSiv.polyvalFrom h (Spec.GcmSiv.dot (s ^^^ y) h) ys =
      Spec.Gcm.ghashFrom (mulXG h) (Spec.Gcm.mul (s ^^^ y) (mulXG h)) ys
    rw [ih, dot_eq]

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
theorem tagInput_eq_tagInputG (a n pt d : List Byte) :
    Spec.GcmSiv.tagInput a n pt d = Words.tagInputG a n pt d := by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, polyvalFrom_eq]
  rfl

end VG.Proof.GcmSiv.Polyval
