module

public import VerifiedGarbage.Proof.Gcm.Clmul.Arith
public import VerifiedGarbage.TCB.AArch64.Simd
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH with the 8-bit PMULL on AArch64: the arithmetic

Untrusted: everything here is checked by Lean. `pmull` of eight pairs of
bytes (`pmB`) multiplies polynomials lane by lane; fifteen of them, of the
two factors shifted by whole bytes in opposite directions, add up to the
product of two doublewords (`polyMul`, what the 64-bit `pmull` computes).
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword

namespace VG.Proof.Gcm.AArch64.Neon

open Polynomial
open VG.AArch64 (polyMul8 ofVHalves)
open VG.VectorCrypto VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul

/-! ## The product of two bytes -/

theorem gp_shl8 (b : BitVec 8) {j : Nat} (hj : j < 8) :
    gp ((b.setWidth 16) <<< j) = X ^ (8 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 8 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 16 - 8 ≤ d + j by omega_using [h]), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega_using [hj]))
  · simp only [h, ite_false, decide_eq_false (show ¬ 16 - 8 ≤ d + j by omega_using [h]), Bool.false_and]; rfl

/-- The first `k` steps of `polyMul8`. -/
def clSteps8 (a b : BitVec 8) (k : Nat) : BitVec 16 :=
  (List.range k).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 16 <<< i) else acc) 0

theorem gp_clSteps8 (a b : BitVec 8) {k : Nat} (hk : k ≤ 8) :
    gp (clSteps8 a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (7 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [clSteps8, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : clSteps8 a b (k + 1) =
        if a.getLsbD k then clSteps8 a b k ^^^ (b.setWidth 16 <<< k) else clSteps8 a b k := by
      simp only [clSteps8, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega_using [hk]), gp_shl8 b (by omega_using [hk]),
        show 8 - k = 7 - k + 1 by omega_using [hk], pow_succ]
      ring
    · rw [ih (by omega_using [hk])]; ring

theorem gp_lsb8 (a : BitVec 8) :
    (∑ i ∈ Finset.range 8, if a.getLsbD i then (X : P) ^ (7 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega_using [hi]), Bool.true_and,
    show 8 - 1 - i = 7 - i by omega_using [], show 7 - (8 - 1 - i) = i by omega_using [hi]]

/-- `pmull` of two bytes multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_polyMul8 (a b : BitVec 8) : gp (polyMul8 a b) = X * gp a * gp b := by
  rw [show polyMul8 a b = clSteps8 a b 8 from rfl, gp_clSteps8 a b (Nat.le_refl _), gp_lsb8]

/-! ## Bytes -/

/-- Byte `i` of a doubleword. -/
def by8 (q : BitVec 64) (i : Nat) : BitVec 8 := q.extractLsb' (8 * i) 8

theorem bytes64 (q : BitVec 64) :
    q = by8 q 7 ++ by8 q 6 ++ by8 q 5 ++ by8 q 4 ++ by8 q 3 ++ by8 q 2 ++ by8 q 1 ++ by8 q 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [by8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have h : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨
      (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_using []
  rcases h with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_using [h, hi]) only [↓ite_eq_left, ↓ite_eq_right, Bool.true_and, decide_eq_true] <;> exact congrArg _ (by omega_using [h, hi])

/-- A doubleword's polynomial, from its bytes'. -/
theorem gp_bytes (q : BitVec 64) :
    gp q = X ^ 56 * gp (by8 q 0) + X ^ 48 * gp (by8 q 1) + X ^ 40 * gp (by8 q 2) +
      X ^ 32 * gp (by8 q 3) + X ^ 24 * gp (by8 q 4) + X ^ 16 * gp (by8 q 5) + X ^ 8 * gp (by8 q 6) +
      gp (by8 q 7) := by
  conv_lhs => rw [bytes64 q]
  simp only [gp_append]
  ring

theorem by8_ushr (q : BitVec 64) (d i : Nat) :
    by8 (q >>> (8 * d)) i = if i + d < 8 then by8 q (i + d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and,
      BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge q _ (by omega_using [h])

theorem by8_shl (q : BitVec 64) (d i : Nat) :
    by8 (q <<< (8 * d)) i = if d ≤ i ∧ i < 8 then by8 q (i - d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and,
      decide_eq_true (show 8 * i + k < 64 by omega_using [h, hk]),
      decide_eq_false (show ¬ 8 * i + k < 8 * d by omega_using [h]), Bool.not_false]
    exact congrArg _ (by omega_using [h])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases h8 : i < 8
    · simp only [decide_eq_true (show 8 * i + k < 8 * d by omega_using [h, h8, hk]), Bool.not_true, Bool.false_and,
        Bool.and_false, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    · simp only [decide_eq_false (show ¬ 8 * i + k < 64 by omega_using [h8]), Bool.false_and, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]

/-! ## `pmull` of eight pairs of bytes -/

/-- What `pmull .8h` computes from the doublewords it reads. -/
def pmB (a b : BitVec 64) : BitVec 128 := ofVHalves fun e => polyMul8 (by8 a e) (by8 b e)

theorem gp_pmB (a b : BitVec 64) :
    gp (pmB a b) = X * (X ^ 112 * (gp (by8 a 0) * gp (by8 b 0)) + X ^ 96 * (gp (by8 a 1) * gp (by8 b 1)) +
      X ^ 80 * (gp (by8 a 2) * gp (by8 b 2)) + X ^ 64 * (gp (by8 a 3) * gp (by8 b 3)) +
      X ^ 48 * (gp (by8 a 4) * gp (by8 b 4)) + X ^ 32 * (gp (by8 a 5) * gp (by8 b 5)) +
      X ^ 16 * (gp (by8 a 6) * gp (by8 b 6)) + gp (by8 a 7) * gp (by8 b 7)) := by
  simp only [pmB, ofVHalves, gp_append, gp_polyMul8]
  ring

theorem polyMul8_zero_left (b : BitVec 8) : polyMul8 0 b = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, zero_mul, gp_zero])

theorem polyMul8_zero_right (a : BitVec 8) : polyMul8 a 0 = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, gp_zero])

/-- The top byte of `pmB` is of the product of the top bytes. -/
theorem msb_pmB (a b : BitVec 64) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = (polyMul8 (by8 a 7) (by8 b 7)).getMsbD i := by
  simp only [pmB, ofVHalves, BitVec.getMsbD_append]
  simp (disch := omega_using [hi]) only [↓ite_eq_right]

theorem msb_pmB_left (a b : BitVec 64) (h : by8 a 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_left]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

theorem msb_pmB_right (a b : BitVec 64) (h : by8 b 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_right]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

/-- A shift up by a byte divides by `X⁸`, if that byte is clear. -/
theorem gp_shl_byte (v : BitVec 128) (h : ∀ i < 8, v.getMsbD i = false) :
    X ^ 8 * gp (v <<< 8) = gp v := by
  ext d
  rw [coeff_X_pow_mul', coeff_gp, coeff_gp, BitVec.getMsbD_shiftLeft]
  by_cases h8 : 8 ≤ d
  · simp only [h8, ite_true, Nat.sub_add_cancel h8]
  · simp only [h8, ite_false, h d (by omega_using [h8])]; rfl

/-! ## The product of two doublewords

Byte `i` of `a` and byte `j` of `b` meet in lane `l` of a `pmull` of `a`
shifted down by `d` bytes and `b` shifted up by as many, where `i = l + d` and
`j = l - d`: their product then lies at byte `2 l = i + j`, where it belongs
(`cl0`: the pairs with `i + j` even). Those with `i + j` odd meet in the
`pmull`s of `a` shifted down by `d` and `b` shifted up by `d - 1`, a byte
below where they belong (`cl1`). -/

def cl0 (a b : BitVec 64) : BitVec 128 :=
  pmB a b ^^^ pmB (a >>> 8) (b <<< 8) ^^^ pmB (a >>> 16) (b <<< 16) ^^^ pmB (a >>> 24) (b <<< 24) ^^^
    pmB (a <<< 8) (b >>> 8) ^^^ pmB (a <<< 16) (b >>> 16) ^^^ pmB (a <<< 24) (b >>> 24)

def cl1 (a b : BitVec 64) : BitVec 128 :=
  pmB a (b >>> 8) ^^^ pmB (a >>> 8) b ^^^ pmB (a >>> 16) (b <<< 8) ^^^ pmB (a >>> 24) (b <<< 16) ^^^
    pmB (a >>> 32) (b <<< 24) ^^^ pmB (a <<< 8) (b >>> 16) ^^^ pmB (a <<< 16) (b >>> 24) ^^^
    pmB (a <<< 24) (b >>> 32)

theorem by8_ushr8 (q : BitVec 64) (i : Nat) : by8 (q >>> 8) i = if i + 1 < 8 then by8 q (i + 1) else 0 :=
  by8_ushr q 1 i
theorem by8_ushr16 (q : BitVec 64) (i : Nat) : by8 (q >>> 16) i = if i + 2 < 8 then by8 q (i + 2) else 0 :=
  by8_ushr q 2 i
theorem by8_ushr24 (q : BitVec 64) (i : Nat) : by8 (q >>> 24) i = if i + 3 < 8 then by8 q (i + 3) else 0 :=
  by8_ushr q 3 i
theorem by8_ushr32 (q : BitVec 64) (i : Nat) : by8 (q >>> 32) i = if i + 4 < 8 then by8 q (i + 4) else 0 :=
  by8_ushr q 4 i
theorem by8_shl8 (q : BitVec 64) (i : Nat) : by8 (q <<< 8) i = if 1 ≤ i ∧ i < 8 then by8 q (i - 1) else 0 :=
  by8_shl q 1 i
theorem by8_shl16 (q : BitVec 64) (i : Nat) : by8 (q <<< 16) i = if 2 ≤ i ∧ i < 8 then by8 q (i - 2) else 0 :=
  by8_shl q 2 i
theorem by8_shl24 (q : BitVec 64) (i : Nat) : by8 (q <<< 24) i = if 3 ≤ i ∧ i < 8 then by8 q (i - 3) else 0 :=
  by8_shl q 3 i

theorem msb_cl1 (a b : BitVec 64) {i : Nat} (hi : i < 8) : (cl1 a b).getMsbD i = false := by
  simp only [cl1, BitVec.getMsbD_xor]
  rw [msb_pmB_right _ _ (by rw [by8_ushr8]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr8]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr16]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr24]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr32]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr16]; rfl) hi,
    msb_pmB_right _ _ (by rw [by8_ushr24]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr32]; rfl) hi]
  rfl

/-- Fifteen `pmull`s of bytes make the `pmull` of two doublewords. -/
theorem cl_polyMul (a b : BitVec 64) : cl0 a b ^^^ (cl1 a b <<< 8) = polyMul a b := by
  apply gp_ext
  apply mul_left_cancel₀ (pow_ne_zero 8 (X_ne_zero (R := ZMod 2)))
  rw [gp_xor, mul_add, gp_shl_byte _ fun i hi => msb_cl1 a b hi, gp_polyMul, gp_bytes a, gp_bytes b]
  simp only [cl0, cl1, gp_xor, gp_pmB, by8_ushr8, by8_ushr16, by8_ushr24, by8_ushr32, by8_shl8, by8_shl16,
    by8_shl24, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, and_true, and_self, ↓reduceIte, gp_zero, zero_mul, mul_zero, add_zero, zero_add]
  ring

end VG.Proof.Gcm.AArch64.Neon
