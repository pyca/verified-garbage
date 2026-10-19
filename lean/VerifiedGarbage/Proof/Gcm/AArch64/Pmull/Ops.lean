module

import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# GHASH with PMULL: the values

What the instructions of `Impl.Gcm.AArch64.Pmull` compute, as bits: the
doublewords of a vector, `ext #8`, the products `acc` accumulates and the
block `reduce` computes from them, and `rev64 .16b`. Their classes in the ring
of `Proof/Gcm/Poly.lean` are in `Arith.lean`; this module needs no algebra.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Pmull

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (poly xInv2Hi)

theorem vdwords (v : BitVec 128) : v = vdword v 1 ++ vdword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, Nat.mul_zero, Nat.zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_append_0 (a b : BitVec 64) : vdword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem vdword_append_1 (a b : BitVec 64) : vdword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.mul_one, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem vdword_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword, BitVec.extractLsb'_xor]

/-! ## `ext #8` -/

/-- `ext d, n, m, #8`: the high half of `n`, then the low half of `m`. -/
def ext8 (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> 64).extractLsb' 0 128

theorem ext8_eq (n m : BitVec 128) : ext8 n m = vdword m 0 ++ vdword n 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ext8, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true, show 64 + i < 128 by omega, decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 64 + i < 128 by omega, decide_eq_true (show i - 64 < 64 by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_ext8_0 (n m : BitVec 128) : vdword (ext8 n m) 0 = vdword n 1 := by
  rw [ext8_eq, vdword_append_0]

theorem vdword_ext8_1 (n m : BitVec 128) : vdword (ext8 n m) 1 = vdword m 0 := by
  rw [ext8_eq, vdword_append_1]

theorem ext8_ext8 (v : BitVec 128) : ext8 (ext8 v v) (ext8 v v) = v := by
  rw [ext8_eq (ext8 v v), vdword_ext8_0, vdword_ext8_1, ← vdwords]

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- The four products of `acc`, of the block `a` as loaded and the key `t`
(`s` its halves swapped), added to `p`. -/
def acc (p : Prod) (a s t : BitVec 128) : Prod :=
  ⟨p.lo ^^^ polyMul (vdword a 1) (vdword s 1),
   p.mid ^^^ polyMul (vdword a 0) (vdword t 0) ^^^ polyMul (vdword a 1) (vdword t 1),
   p.hi ^^^ polyMul (vdword a 0) (vdword s 0)⟩

def zero : Prod := ⟨0, 0, 0⟩

end Prod

/-- The block, with its halves swapped, that `reduce` computes from a product:
`swap(hi ⊕ fold(u)) = swap(hi) ⊕ u ⊕ swap(pmull(u₀, 0xc2 · 2⁵⁶))` for
`u = mid ⊕ fold(lo)`. -/
def reduce (p : Prod) : BitVec 128 :=
  let u := (p.mid ^^^ ext8 p.lo p.lo) ^^^ polyMul (vdword p.lo 0) poly
  (ext8 p.hi p.hi ^^^ u) ^^^ ext8 (polyMul (vdword u 0) poly) (polyMul (vdword u 0) poly)

/-- `x⁻²` (reflected). -/
def xInv2 : BitVec 128 := xInv2Hi ++ 3#64

/-! ## Loads and stores -/

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat}
    (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

/-- `rev64 .16b` reverses the bytes of each doubleword. -/
theorem vdword_rev64b (v : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VRevOp.eval .rev64b v) e = rev64 (vdword v e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hr : rev64 (vdword v e) = byteRev64 (vdword v e) := rfl
  rw [hr, getLsbD_byteRev64 _ _ hi]
  simp only [vdword, VRevOp.eval, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * (7 - i / 8) + i % 8 < 64 by omega]
  rw [show 64 * e + i = 8 * (8 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (Nat.mod_lt _ (by decide)), vbyte, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  exact congrArg _ (by omega)

theorem rev64b_rev64b (v : BitVec 128) : VRevOp.eval .rev64b (VRevOp.eval .rev64b v) = v := by
  have h : ∀ a : BitVec 64, rev64 (rev64 a) = a := byteRev64_byteRev64
  rw [vdwords (VRevOp.eval .rev64b _), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), h, h, ← vdwords]

end VG.Proof.Gcm.AArch64.Pmull
