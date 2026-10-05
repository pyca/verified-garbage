import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.AArch64.Target

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Arith`. -/
section

/-!
# GHASH with PMULL: the arithmetic

What the instructions of `Impl.Gcm.AArch64.Pmull` compute, in the ring `Q` of
`Proof/Gcm/Poly.lean` (as `Proof/Gcm/X86_64/Pclmul/Ghash.lean` does for
PCLMULQDQ):

* `pmull` multiplies polynomials (`φ_polyMul`), so the four of `acc`
  compute `x · a · t` as a 256-bit value (`Prod.val_acc`), where `a` is a
  block as loaded (its halves swapped: its class is `ρ a`);
* `reduce` maps a 256-bit value to a block of the same class, with its
  halves swapped (`ρ_reduce`);
* `rev64 .16b` of a 16-byte load is the block as loaded (`ρ_load`), and
  undoes itself (`rev64b_rev64b`).
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open Polynomial
open VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (poly xInv2Hi)

/-! ## Carry-less multiplication -/

theorem gp_shl (b : BitVec 64) {j : Nat} (hj : j < 64) :
    gp ((b.setWidth 128) <<< j) = X ^ (64 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 64 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 128 - 64 ≤ d + j by omega), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [h, ite_false, decide_eq_false (show ¬ 128 - 64 ≤ d + j by omega), Bool.false_and]; rfl

/-- The first `k` steps of `polyMul`. -/
def clSteps (a b : BitVec 64) (k : Nat) : BitVec 128 :=
  (List.range k).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 128 <<< i) else acc) 0

theorem gp_clSteps (a b : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    gp (VG.Proof.Gcm.AArch64.Pmull.clSteps a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (63 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [VG.Proof.Gcm.AArch64.Pmull.clSteps, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : VG.Proof.Gcm.AArch64.Pmull.clSteps a b (k + 1) =
        if a.getLsbD k then VG.Proof.Gcm.AArch64.Pmull.clSteps a b k ^^^ (b.setWidth 128 <<< k) else VG.Proof.Gcm.AArch64.Pmull.clSteps a b k := by
      simp only [VG.Proof.Gcm.AArch64.Pmull.clSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega), VG.Proof.Gcm.AArch64.Pmull.gp_shl b (by omega),
        show 64 - k = 63 - k + 1 by omega, pow_succ]
      ring
    · rw [ih (by omega)]; ring

theorem gp_lsb (a : BitVec 64) :
    (∑ i ∈ Finset.range 64, if a.getLsbD i then (X : P) ^ (63 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega), Bool.true_and,
    show 64 - 1 - i = 63 - i by omega, show 63 - (64 - 1 - i) = i by omega]

/-- `pmull` multiplies polynomials (with the factor `X` of the reflected
representation). -/
theorem gp_polyMul (a b : BitVec 64) : gp (polyMul a b) = X * gp a * gp b := by
  rw [show polyMul a b = VG.Proof.Gcm.AArch64.Pmull.clSteps a b 64 from rfl, VG.Proof.Gcm.AArch64.Pmull.gp_clSteps a b (Nat.le_refl _), VG.Proof.Gcm.AArch64.Pmull.gp_lsb]

/-! ## Doublewords -/

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem φ_polyMul (a b : BitVec 64) : φ (polyMul a b) = x * VG.Proof.Gcm.AArch64.Pmull.ψ a * VG.Proof.Gcm.AArch64.Pmull.ψ b := by
  simp only [φ, VG.Proof.Gcm.AArch64.Pmull.ψ, VG.Proof.Gcm.AArch64.Pmull.gp_polyMul, map_mul, AdjoinRoot.mk_X]

theorem ψ_xor (a b : BitVec 64) : VG.Proof.Gcm.AArch64.Pmull.ψ (a ^^^ b) = VG.Proof.Gcm.AArch64.Pmull.ψ a + VG.Proof.Gcm.AArch64.Pmull.ψ b := by
  simp only [VG.Proof.Gcm.AArch64.Pmull.ψ, gp_xor, map_add]

theorem φ_append (a b : BitVec 64) : φ (a ++ b) = VG.Proof.Gcm.AArch64.Pmull.ψ a + x ^ 64 * VG.Proof.Gcm.AArch64.Pmull.ψ b := by
  simp only [φ, VG.Proof.Gcm.AArch64.Pmull.ψ, gp_append, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

theorem vdwords (v : BitVec 128) : v = vdword v 1 ++ vdword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, mul_zero, zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_append_0 (a b : BitVec 64) : vdword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, mul_zero, zero_add, ite_true]

theorem vdword_append_1 (a b : BitVec 64) : vdword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, mul_one, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem vdword_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword, BitVec.extractLsb'_xor]

theorem φ_v (v : BitVec 128) : φ v = VG.Proof.Gcm.AArch64.Pmull.ψ (vdword v 1) + x ^ 64 * VG.Proof.Gcm.AArch64.Pmull.ψ (vdword v 0) := by
  conv => lhs; rw [VG.Proof.Gcm.AArch64.Pmull.vdwords v]
  rw [VG.Proof.Gcm.AArch64.Pmull.φ_append]

/-- The class of a block as loaded (its halves swapped). -/
noncomputable def ρ (v : BitVec 128) : Q := VG.Proof.Gcm.AArch64.Pmull.ψ (vdword v 0) + x ^ 64 * VG.Proof.Gcm.AArch64.Pmull.ψ (vdword v 1)

theorem ρ_xor (a b : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.ρ (a ^^^ b) = VG.Proof.Gcm.AArch64.Pmull.ρ a + VG.Proof.Gcm.AArch64.Pmull.ρ b := by
  simp only [VG.Proof.Gcm.AArch64.Pmull.ρ, VG.Proof.Gcm.AArch64.Pmull.vdword_xor, VG.Proof.Gcm.AArch64.Pmull.ψ_xor]; ring

/-! ## `ext #8` -/

/-- `ext d, n, m, #8`: the high half of `n`, then the low half of `m`. -/
def ext8 (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> 64).extractLsb' 0 128

theorem ext8_eq (n m : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.ext8 n m = vdword m 0 ++ vdword n 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Gcm.AArch64.Pmull.ext8, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true, show 64 + i < 128 by omega, decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 64 + i < 128 by omega, decide_eq_true (show i - 64 < 64 by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_ext8_0 (n m : BitVec 128) : vdword (VG.Proof.Gcm.AArch64.Pmull.ext8 n m) 0 = vdword n 1 := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ext8_eq, VG.Proof.Gcm.AArch64.Pmull.vdword_append_0]

theorem vdword_ext8_1 (n m : BitVec 128) : vdword (VG.Proof.Gcm.AArch64.Pmull.ext8 n m) 1 = vdword m 0 := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ext8_eq, VG.Proof.Gcm.AArch64.Pmull.vdword_append_1]

theorem φ_ext8 (n m : BitVec 128) : φ (VG.Proof.Gcm.AArch64.Pmull.ext8 n m) = VG.Proof.Gcm.AArch64.Pmull.ψ (vdword m 0) + x ^ 64 * VG.Proof.Gcm.AArch64.Pmull.ψ (vdword n 1) := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ext8_eq, VG.Proof.Gcm.AArch64.Pmull.φ_append]

/-- A block with its halves swapped, as loaded. -/
theorem ρ_ext8_self (v : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.ρ (VG.Proof.Gcm.AArch64.Pmull.ext8 v v) = φ v := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ρ, VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_0, VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_1, VG.Proof.Gcm.AArch64.Pmull.φ_v]

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : VG.Proof.Gcm.AArch64.Pmull.Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

/-- The four products of `acc`, of the block `a` as loaded and the key `t`
(`s` its halves swapped), added to `p`. -/
def acc (p : VG.Proof.Gcm.AArch64.Pmull.Prod) (a s t : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.Prod :=
  ⟨p.lo ^^^ polyMul (vdword a 1) (vdword s 1),
   p.mid ^^^ polyMul (vdword a 0) (vdword t 0) ^^^ polyMul (vdword a 1) (vdword t 1),
   p.hi ^^^ polyMul (vdword a 0) (vdword s 0)⟩

def zero : VG.Proof.Gcm.AArch64.Pmull.Prod := ⟨0, 0, 0⟩

theorem val_zero : zero.val = 0 := by
  simp only [VG.Proof.Gcm.AArch64.Pmull.Prod.val, VG.Proof.Gcm.AArch64.Pmull.Prod.zero, BitVec.ofNat_eq_ofNat, φ_zero', mul_zero, add_zero]

theorem val_acc (p : VG.Proof.Gcm.AArch64.Pmull.Prod) (a t : BitVec 128) :
    (p.acc a (VG.Proof.Gcm.AArch64.Pmull.ext8 t t) t).val = p.val + x * VG.Proof.Gcm.AArch64.Pmull.ρ a * φ t := by
  simp only [VG.Proof.Gcm.AArch64.Pmull.Prod.acc, VG.Proof.Gcm.AArch64.Pmull.Prod.val, φ_xor, VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_0, VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_1, VG.Proof.Gcm.AArch64.Pmull.φ_polyMul, VG.Proof.Gcm.AArch64.Pmull.ρ, VG.Proof.Gcm.AArch64.Pmull.φ_v t]
  ring

end Prod

/-! ## The reduction -/

theorem ψ_poly : VG.Proof.Gcm.AArch64.Pmull.ψ poly = 1 + x + x ^ 6 := by
  have hb : ∀ d < 64, poly.getMsbD d = (d = 0 || d = 1 || d = 6) := by decide +kernel
  have h : gp poly = 1 + X + X ^ 6 := by
    ext d
    rw [coeff_gp]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    by_cases hd : d < 64
    · rw [hb d hd]
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6)) with
        rfl | rfl | rfl | ⟨h0, h1, h6⟩
      · decide
      · decide
      · decide
      · simp only [VG.Proof.Gcm.Poly.bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte,
          show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : poly.getMsbD d = false := by
        simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
        omega
      rw [e]
      simp only [VG.Proof.Gcm.Poly.bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega,
        show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega]
  simp only [VG.Proof.Gcm.AArch64.Pmull.ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem φ_ext8_self (v : BitVec 128) : φ (VG.Proof.Gcm.AArch64.Pmull.ext8 v v) = VG.Proof.Gcm.AArch64.Pmull.ρ v := by rw [VG.Proof.Gcm.AArch64.Pmull.φ_ext8, VG.Proof.Gcm.AArch64.Pmull.ρ]

theorem ext8_ext8 (v : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.ext8 (VG.Proof.Gcm.AArch64.Pmull.ext8 v v) (VG.Proof.Gcm.AArch64.Pmull.ext8 v v) = v := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ext8_eq (VG.Proof.Gcm.AArch64.Pmull.ext8 v v), VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_0, VG.Proof.Gcm.AArch64.Pmull.vdword_ext8_1, ← VG.Proof.Gcm.AArch64.Pmull.vdwords]

/-- A block as loaded, plus the `pmull` of its low half by `0xc2 · 2⁵⁶`, is of
the class of `x⁶⁴` times the block. -/
theorem ρ_add_polyMul (u : BitVec 128) : VG.Proof.Gcm.AArch64.Pmull.ρ u + φ (polyMul (vdword u 0) poly) = x ^ 64 * φ u := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ρ, VG.Proof.Gcm.AArch64.Pmull.φ_polyMul, VG.Proof.Gcm.AArch64.Pmull.ψ_poly, VG.Proof.Gcm.AArch64.Pmull.φ_v u]
  linear_combination (-VG.Proof.Gcm.AArch64.Pmull.ψ (vdword u 0)) * x128

/-- `fold(v) = swap(v) ⊕ pmull(v₀, 0xc2 · 2⁵⁶)` is of the class of `x⁶⁴ · v`. -/
theorem φ_fold (v : BitVec 128) : φ (VG.Proof.Gcm.AArch64.Pmull.ext8 v v ^^^ polyMul (vdword v 0) poly) = x ^ 64 * φ v := by
  rw [φ_xor, VG.Proof.Gcm.AArch64.Pmull.φ_ext8_self, VG.Proof.Gcm.AArch64.Pmull.ρ_add_polyMul]

/-- The block, with its halves swapped, that `reduce` computes from a product:
`swap(hi ⊕ fold(u)) = swap(hi) ⊕ u ⊕ swap(pmull(u₀, 0xc2 · 2⁵⁶))` for
`u = mid ⊕ fold(lo)`. -/
def reduce (p : VG.Proof.Gcm.AArch64.Pmull.Prod) : BitVec 128 :=
  let u := (p.mid ^^^ VG.Proof.Gcm.AArch64.Pmull.ext8 p.lo p.lo) ^^^ polyMul (vdword p.lo 0) poly
  (VG.Proof.Gcm.AArch64.Pmull.ext8 p.hi p.hi ^^^ u) ^^^ VG.Proof.Gcm.AArch64.Pmull.ext8 (polyMul (vdword u 0) poly) (polyMul (vdword u 0) poly)

theorem ρ_reduce (p : VG.Proof.Gcm.AArch64.Pmull.Prod) : VG.Proof.Gcm.AArch64.Pmull.ρ (VG.Proof.Gcm.AArch64.Pmull.reduce p) = p.val := by
  simp only [VG.Proof.Gcm.AArch64.Pmull.reduce]
  rw [VG.Proof.Gcm.AArch64.Pmull.ρ_xor, VG.Proof.Gcm.AArch64.Pmull.ρ_xor, VG.Proof.Gcm.AArch64.Pmull.ρ_ext8_self, VG.Proof.Gcm.AArch64.Pmull.ρ_ext8_self, add_assoc, VG.Proof.Gcm.AArch64.Pmull.ρ_add_polyMul, BitVec.xor_assoc, φ_xor,
    VG.Proof.Gcm.AArch64.Pmull.φ_fold, Prod.val]
  ring

/-! ## `x⁻²` -/

/-- `x⁻²` (reflected). -/
def xInv2 : BitVec 128 := xInv2Hi ++ 3#64

theorem gp_xInv2 : gp VG.Proof.Gcm.AArch64.Pmull.xInv2 = X + X ^ 5 + X ^ 6 + X ^ 126 + X ^ 127 := by
  have hb : ∀ d < 128, xInv2.getMsbD d = (d = 1 || d = 5 || d = 6 || d = 126 || d = 127) := by
    decide +kernel
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 1 ∨ d = 5 ∨ d = 6 ∨ d = 126 ∨ d = 127 ∨
      (d ≠ 1 ∧ d ≠ 5 ∧ d ≠ 6 ∧ d ≠ 126 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | rfl | ⟨h1, h5, h6, h126, h127⟩
    · decide
    · decide
    · decide
    · decide
    · decide
    · simp only [VG.Proof.Gcm.Poly.bit, h1, decide_false, h5, Bool.or_self, h6, h126, h127, Bool.false_eq_true,
        ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv2.getMsbD d = false := by
      simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    rw [e]
    simp only [VG.Proof.Gcm.Poly.bit, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d by omega, add_zero,
      show d ≠ 5 by omega, show d ≠ 6 by omega, show d ≠ 126 by omega, show d ≠ 127 by omega]

theorem x2_φ_xInv2 : x ^ 2 * φ VG.Proof.Gcm.AArch64.Pmull.xInv2 = 1 := by
  simp only [φ, VG.Proof.Gcm.AArch64.Pmull.gp_xInv2, map_add, map_pow, AdjoinRoot.mk_X]
  linear_combination (1 + x) * x128 + (x + x ^ 2 + x ^ 3 + x ^ 7 + x ^ 8) * two_Q

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
  simp only [ofVBytes, VG.Proof.Gcm.AArch64.Pmull.getLsbD_append_block _ _ _ hr]
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
    VG.Proof.Gcm.AArch64.Pmull.getLsbD_ofVBytes _ (by omega) (Nat.mod_lt _ (by decide)), vbyte, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  exact congrArg _ (by omega)

theorem rev64b_rev64b (v : BitVec 128) : VRevOp.eval .rev64b (VRevOp.eval .rev64b v) = v := by
  have h : ∀ a : BitVec 64, rev64 (rev64 a) = a := byteRev64_byteRev64
  rw [VG.Proof.Gcm.AArch64.Pmull.vdwords (VRevOp.eval .rev64b _), VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide), VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide),
    VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide), VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide), h, h, ← VG.Proof.Gcm.AArch64.Pmull.vdwords]

end VG.Proof.Gcm.AArch64.Pmull

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash`. -/
section

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups`.
section

/-!
# GHASH with PMULL: the instruction groups

What each group of instructions of `Impl.Gcm.AArch64.Pmull` does to the state,
each proved by one symbolic execution for any registers it is used with, and
what a load and a store of a block are in `Q`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)

/-! ## Loads and stores of blocks -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [VG.Proof.Gcm.AArch64.Pmull.getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  rw [VG.Proof.Gcm.AArch64.Pmull.getLsbD_read m 16 p _ (by omega), VG.Proof.Gcm.AArch64.Pmull.getLsbD_read m 8 _ i (by omega), Offset.add_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega, show i % 8 = (64 * e + i) % 8 by omega]

/-- A block, loaded and `rev64`ed. -/
theorem ρ_load (m : Mem) (p : Addr) :
    VG.Proof.Gcm.AArch64.Pmull.ρ (VRevOp.eval .rev64b (m.read p 16)) = φ (Spec.Gcm.blockAt m p) := by
  rw [VG.Proof.Gcm.AArch64.Pmull.ρ, VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide), VG.Proof.Gcm.AArch64.Pmull.vdword_rev64b _ (by decide), VG.Proof.Gcm.AArch64.Pmull.vdword_read16 m p (by decide),
    VG.Proof.Gcm.AArch64.Pmull.vdword_read16 m p (by decide), ← blockAt_rev, VG.Proof.Gcm.AArch64.Pmull.φ_append]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec (8 * 16)) : (m.write p 16 v).read p 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

/-- A block as loaded, `rev64`ed and stored. -/
theorem φ_store (m : Mem) (p : Addr) (v : BitVec 128) :
    φ (Spec.Gcm.blockAt (m.write p 16 (VRevOp.eval .rev64b v)) p) = VG.Proof.Gcm.AArch64.Pmull.ρ v := by
  rw [← VG.Proof.Gcm.AArch64.Pmull.ρ_load, VG.Proof.Gcm.AArch64.Pmull.read_write16, VG.Proof.Gcm.AArch64.Pmull.rev64b_rev64b]

/-! ## Reading through writes -/

theorem v_setV (s : State) (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.setV d x).v r = if r = d then x else s.v r := rfl

theorem gpr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).gpr = s.gpr := rfl
theorem mem_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).mem = s.mem := rfl
theorem rd_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).rd = s.rd := rfl
theorem wr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).wr = s.wr := rfl
theorem sp_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).sp = s.sp := rfl

/-- `s'` differs from `s` at most in the vector registers `rs`. -/
structure VOnly (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem VOnly.trans {rs rs' : List VReg} {s s' s'' : State} (h : VG.Proof.Gcm.AArch64.Pmull.VOnly rs s s')
    (h' : VG.Proof.Gcm.AArch64.Pmull.VOnly rs' s' s'') : VG.Proof.Gcm.AArch64.Pmull.VOnly (rs ++ rs') s s'' :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1),
   h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem VOnly.weaken {rs rs' : List VReg} {s s' : State} (h : VG.Proof.Gcm.AArch64.Pmull.VOnly rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.Gcm.AArch64.Pmull.VOnly rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem VOnly.refl (rs : List VReg) (s : State) : VG.Proof.Gcm.AArch64.Pmull.VOnly rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The groups -/

/-- The product registers. -/
def prod (s : State) : VG.Proof.Gcm.AArch64.Pmull.Prod := ⟨s.v LO, s.v MID, s.v HI⟩

theorem VOnly.prod {rs : List VReg} {s s' : State} (h : VG.Proof.Gcm.AArch64.Pmull.VOnly rs s s') (h3 : VReg.v3 ∉ rs)
    (h4 : VReg.v4 ∉ rs) (h5 : VReg.v5 ∉ rs) : Pmull.prod s' = Pmull.prod s := by
  simp only [Pmull.prod, h.v _ h3, h.v _ h4, h.v _ h5]

/-- A register `acc` only reads. -/
def Free (r : VReg) : Prop := r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v7

theorem exec_pmull0 (d n m : VReg) (s : State) :
    exec (.vop (.pmull false d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 0) (vdword (s.v m) 0))) := rfl

theorem exec_pmull1 (d n m : VReg) (s : State) :
    exec (.vop (.pmull true d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 1) (vdword (s.v m) 1))) := rfl

theorem exec_eor (d n m : VReg) (s : State) :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_ext8 (d n m : VReg) (s : State) :
    exec (.vop (.ext d n m 8)) s = some (s.setV d (VG.Proof.Gcm.AArch64.Pmull.ext8 (s.v n) (s.v m))) := rfl

theorem exec_movi0 (d : VReg) (s : State) : exec (.vop (.movi0 d)) s = some (s.setV d 0) := rfl

theorem exec_rev64b (d n : VReg) (s : State) :
    exec (.vop (.rev .rev64b d n)) s = some (s.setV d (VRevOp.eval .rev64b (s.v n))) := rfl

theorem exec_ldrq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.load, hin,
    Option.map_some]

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.zero) s fun s' =>
      VG.Proof.Gcm.AArch64.Pmull.prod s' = Prod.zero ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.zero, runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.AArch64.Pmull.exec_movi0,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [VG.Proof.Gcm.AArch64.Pmull.prod, VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (a sk t : VReg) (s : State) (ha : VG.Proof.Gcm.AArch64.Pmull.Free a) (hs : VG.Proof.Gcm.AArch64.Pmull.Free sk) (ht : VG.Proof.Gcm.AArch64.Pmull.Free t) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.acc a sk t)) s fun s' =>
      VG.Proof.Gcm.AArch64.Pmull.prod s' = (VG.Proof.Gcm.AArch64.Pmull.prod s).acc (s.v a) (s.v sk) (s.v t) ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI, T] s s' := by
  obtain ⟨ha3, ha4, ha5, ha7⟩ := ha
  obtain ⟨-, -, hs5, hs7⟩ := hs
  obtain ⟨ht3, ht4, ht5, ht7⟩ := ht
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.acc, runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.AArch64.Pmull.exec_pmull0,
    VG.Proof.Gcm.AArch64.Pmull.exec_pmull1, VG.Proof.Gcm.AArch64.Pmull.exec_eor, Option.some.injEq, exists_eq_left', VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true, ite_false,
    reduceCtorEq, ha3, ha4, ha5, ha7, hs5, hs7, ht3, ht4, ht5, ht7]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [VG.Proof.Gcm.AArch64.Pmull.prod, Prod.acc, VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : VReg) (s : State) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.reduce d)) s fun s' =>
      s'.v d = VG.Proof.Gcm.AArch64.Pmull.reduce (VG.Proof.Gcm.AArch64.Pmull.prod s) ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI, T, d] s s' := by
  have hc0 : vdword (ofVDwords poly poly) 0 = poly := VG.Proof.Gcm.AArch64.Pmull.vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.reduce, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Gcm.AArch64.Pmull.exec_pmull0, VG.Proof.Gcm.AArch64.Pmull.exec_eor, VG.Proof.Gcm.AArch64.Pmull.exec_ext8, Option.some.injEq, exists_eq_left', VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true,
    ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [hc0]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `d ← mul(a, t)` with its halves swapped, a block of class `x · a · t` (`a` as loaded). -/
theorem mul_ok (d a sk t : VReg) (s : State) (ha : VG.Proof.Gcm.AArch64.Pmull.Free a) (hs : VG.Proof.Gcm.AArch64.Pmull.Free sk) (ht : VG.Proof.Gcm.AArch64.Pmull.Free t)
    (hst : s.v sk = VG.Proof.Gcm.AArch64.Pmull.ext8 (s.v t) (s.v t)) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.mul d a sk t)) s fun s' =>
      VG.Proof.Gcm.AArch64.Pmull.ρ (s'.v d) = x * VG.Proof.Gcm.AArch64.Pmull.ρ (s.v a) * φ (s.v t) ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI, T, d] s s' := by
  rw [Impl.Gcm.AArch64.Pmull.mul, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.acc_ok a sk t s₁ ha hs ht) fun s₂ ⟨p₂, o₂⟩ => ?_
  have k : ∀ r, r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 → s₂.v r = s.v r := fun r h3 h4 h5 h7 => by
    rw [o₂.v r (by simp [h3, h4, h5, h7]), o₁.v r (by simp [h3, h4, h5])]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.reduce_ok d s₂ (by rw [k C (by decide) (by decide) (by decide) (by decide), hc]))
    fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, VG.Proof.Gcm.AArch64.Pmull.ρ_reduce, p₂, p₁, o₁.v a (by simp [ha.1, ha.2.1, ha.2.2.1]),
      o₁.v sk (by simp [hs.1, hs.2.1, hs.2.2.1]), o₁.v t (by simp [ht.1, ht.2.1, ht.2.2.1]), hst,
      Prod.val_acc, Prod.val_zero, zero_add]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

/-- `ext d, n, n, #8`: the halves of `n`, swapped. -/
theorem swap_ok (d n : VReg) (s : State) :
    WP isa (.block [.vop (.ext d n n 8)]) s fun s' =>
      s'.v d = VG.Proof.Gcm.AArch64.Pmull.ext8 (s.v n) (s.v n) ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.AArch64.Pmull.exec_ext8, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr, ite_false]

/-- A 16-byte load at `[n, #off]`, and `rev64`. -/
theorem ldrev_ok (d : VReg) (n : Reg) (off : Nat) (s : State) (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev d n off)) s fun s' =>
      VG.Proof.Gcm.AArch64.Pmull.ρ (s'.v d) = φ (Spec.Gcm.blockAt s.mem (s.gpr n + BitVec.ofNat 64 off)) ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.loadRev, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Gcm.AArch64.Pmull.exec_ldrq ho ho' hin, VG.Proof.Gcm.AArch64.Pmull.exec_rev64b,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true, VG.Proof.Gcm.AArch64.Pmull.ρ_load]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr, ite_false]

theorem exec_strq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.store, hout]

/-- `eor d, n, m`. -/
theorem eor_ok (d n m : VReg) (s : State) :
    WP isa (.block [.vop (.logic .eor d n m)]) s fun s' =>
      s'.v d = s.v n ^^^ s.v m ∧ VG.Proof.Gcm.AArch64.Pmull.VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.AArch64.Pmull.exec_eor, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [VG.Proof.Gcm.AArch64.Pmull.gpr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.rd_setV],
    by simp only [VG.Proof.Gcm.AArch64.Pmull.wr_setV], by simp only [VG.Proof.Gcm.AArch64.Pmull.sp_setV]⟩⟩
  · simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [VG.Proof.Gcm.AArch64.Pmull.v_setV, hr, ite_false]

/-! ## General-purpose registers and constants -/

theorem v_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) : (s.write sz r w).v = s.v := rfl
theorem mem_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).mem = s.mem := rfl
theorem rd_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).rd = s.rd := rfl
theorem wr_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).wr = s.wr := rfl

theorem exec_movz_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) (s : State) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, h, ite_true]

theorem exec_dup_d2 (d : VReg) (n : Reg) (s : State) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem exec_ins_d2 {d : VReg} {i : Nat} {n : Reg} (h : i < 2) (s : State) :
    exec (.vop (.ins .d2 d i n)) s = some (s.setV d (setLane (s.v d) 64 i (s.gpr n))) := by
  simp only [exec, VOp.eval, h, ite_true, Option.map_some]

theorem setLane_pair (v : BitVec 128) (a b : BitVec 64) :
    setLane (setLane v 64 0 a) 64 1 b = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.mul_zero, Nat.mul_one, Nat.sub_zero]
  by_cases h : j < 64
  · simp only [h, decide_true, ite_true]
    simp
  · simp only [h, decide_false, ite_false, show j - 64 < 64 by omega, show j - 64 < 128 by omega]
    simp [show 64 ≤ j by omega]

theorem gpr_write_x (s : State) (d : Reg) (w : BitVec 64) (r : Reg) :
    (s.write .x d w).gpr r = if r = d then w else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- The reduction constant, zero, and `x⁻²` in both orders. -/
theorem consts_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' =>
      s'.v C = ofVDwords poly poly ∧ s'.v (tReg 2) = VG.Proof.Gcm.AArch64.Pmull.xInv2 ∧
      s'.v (sReg 2) = VG.Proof.Gcm.AArch64.Pmull.ext8 VG.Proof.Gcm.AArch64.Pmull.xInv2 VG.Proof.Gcm.AArch64.Pmull.xInv2 ∧
      (∀ r, r ≠ C → r ≠ tReg 2 → r ≠ sReg 2 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 3 < 64 by decide), VG.Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 0 < 64 by decide),
    VG.Proof.Gcm.AArch64.Pmull.exec_dup_d2, VG.Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 0 < 2 by decide), VG.Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 1 < 2 by decide),
    VG.Proof.Gcm.AArch64.Pmull.v_setV, VG.Proof.Gcm.AArch64.Pmull.gpr_setV, VG.Proof.Gcm.AArch64.Pmull.v_write, VG.Proof.Gcm.AArch64.Pmull.gpr_write_x, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', VG.Proof.Gcm.AArch64.Pmull.setLane_pair, VG.Proof.Gcm.AArch64.Pmull.mem_setV, VG.Proof.Gcm.AArch64.Pmull.rd_setV, VG.Proof.Gcm.AArch64.Pmull.wr_setV, VG.Proof.Gcm.AArch64.Pmull.mem_write,
    VG.Proof.Gcm.AArch64.Pmull.rd_write, VG.Proof.Gcm.AArch64.Pmull.wr_write, and_true]
  refine ⟨by decide, by decide, by rw [VG.Proof.Gcm.AArch64.Pmull.ext8_eq]; decide, fun r hc ht hs => ?_,
    fun r h5 h6 h7 => ?_⟩
  · simp only [hc, ht, hs, ite_false]
  · simp only [h5, h6, h7, ite_false]

theorem exec_addImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_subImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_lsr {d n : Reg} {sh : Nat} (h : sh < 64) (s : State) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, State.read, BitVec.setWidth_eq]

/-- Past `k` blocks. -/
theorem advance_ok (k : Nat) (hk : 16 * k < 4096) (s : State) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.advance k)) s fun s' =>
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 k ∧ s'.gpr .x5 = s'.gpr .x3 >>> 3 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.advance, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Gcm.AArch64.Pmull.exec_addImm hk, VG.Proof.Gcm.AArch64.Pmull.exec_subImm (show k < 4096 by omega), VG.Proof.Gcm.AArch64.Pmull.exec_lsr (show 3 < 64 by decide),
    VG.Proof.Gcm.AArch64.Pmull.gpr_write_x, ite_true,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h2 h3 h5 => by simp only [h2, h3, h5, ite_false], rfl, rfl, rfl, rfl⟩

/-- `lsr d, n, #sh`. -/
theorem lsr_ok (d n : Reg) (sh : Nat) (hsh : sh < 64) (s : State) :
    WP isa (.block [.lsr .x d n sh]) s fun s' =>
      s'.gpr d = s.gpr n >>> sh ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.AArch64.Pmull.exec_lsr hsh, VG.Proof.Gcm.AArch64.Pmull.gpr_write_x, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl⟩

/-! ## The registers of the powers -/

theorem tReg_free (k : Nat) : VG.Proof.Gcm.AArch64.Pmull.Free (tReg k) := by
  unfold tReg VG.Proof.Gcm.AArch64.Pmull.Free; split <;> decide

theorem sReg_free (k : Nat) : VG.Proof.Gcm.AArch64.Pmull.Free (sReg k) := by
  unfold sReg VG.Proof.Gcm.AArch64.Pmull.Free; split <;> decide

/-- The registers of the powers are not those of a block's arithmetic or the constants. -/
theorem tReg_nmem (k : Nat) : tReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold tReg; split <;> decide

theorem sReg_nmem (k : Nat) : sReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold sReg; split <;> decide

theorem tReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : tReg k ∉ rs :=
  fun h => VG.Proof.Gcm.AArch64.Pmull.tReg_nmem k (hs _ h)

theorem sReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : sReg k ∉ rs :=
  fun h => VG.Proof.Gcm.AArch64.Pmull.sReg_nmem k (hs _ h)

theorem ne_tReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ tReg k :=
  fun e => VG.Proof.Gcm.AArch64.Pmull.tReg_nmem k (e ▸ h)

theorem ne_sReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ sReg k :=
  fun e => VG.Proof.Gcm.AArch64.Pmull.sReg_nmem k (e ▸ h)

theorem tReg_ne_sReg (i j : Nat) : tReg i ≠ sReg j := by
  unfold tReg sReg; split <;> split <;> decide

theorem tReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → tReg i = tReg j → i = j := by decide

theorem sReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → sReg i = sReg j → i = j := by decide

end VG.Proof.Gcm.AArch64.Pmull

end

/-!
# GHASH with PMULL: the whole function

`ghash_verified` proves `Impl.Gcm.AArch64.Pmull.ghash` against
`Proof.Gcm.ghashAArch64` (the contract of `vg_ghash`,
`Proof/Gcm/AArch64/Ghash.lean`).

The registers `tReg k` hold `Tₖ` with `x · Tₖ = Hᵏ` (`k = 1 …`, up to 8
once the powers are computed), so that `mul(a, Tₖ) = a · Hᵏ`, `sReg k` the
same with its halves swapped, and `v0` holds `Y` after `i` blocks, as
loaded; the memory is not written until the epilogue stores `Y`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## `Y` and the blocks -/

/-- `Y` after `i` blocks. -/
abbrev Ys (s₀ : State) (i : Nat) : VG.Spec.Gcm.Block :=
  ghashFrom (H₀ s₀) (Y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (dp s₀) i)

theorem φ_Ys_succ (s₀ : State) (i : Nat) :
    φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ (i + 1)) = (φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i) + φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) := by
  rw [VG.Proof.Gcm.AArch64.Pmull.Ys, ghashFrom_blocksAt_succ, φ_mul, φ_xor]

/-- Block `i + j` is in the data. -/
theorem in_blk16 {s₀ : State} (hp : Pre s₀) {i j : Nat} (h : i + j < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * j)) 16 := by
  have := hp.nb_lt
  refine ⟨dR s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add, ← Nat.mul_add]
  exact contains_offset (by omega) (by omega)

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem shr3_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3).toNat = n / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem shr3_beq {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 == 0) = decide (n < 8) := by
  by_cases h : n < 8
  · have e : BitVec.ofNat 64 n >>> 3 = 0 :=
      BitVec.eq_of_toNat_eq (by rw [VG.Proof.Gcm.AArch64.Pmull.shr3_toNat hn]; show n / 8 = 0; omega)
    rw [e, decide_eq_true h]; rfl
  · have e : BitVec.ofNat 64 n >>> 3 ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [VG.Proof.Gcm.AArch64.Pmull.shr3_toNat hn] at h'
      have : n / 8 = 0 := h'
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false h]

theorem shr_beq {n : Nat} (s : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> s == 0) = decide (n < 2 ^ s) := by
  have h : (BitVec.ofNat 64 n >>> s).toNat = n / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  by_cases hlt : n < 2 ^ s
  · have e : BitVec.ofNat 64 n >>> s = 0 :=
      BitVec.eq_of_toNat_eq (by rw [h]; exact Nat.div_eq_of_lt hlt)
    rw [e, decide_eq_true hlt]; rfl
  · have e : BitVec.ofNat 64 n >>> s ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [h] at h'
      have h0 : n / 2 ^ s = 0 := h'
      have := Nat.div_pos (Nat.le_of_not_lt hlt) (Nat.two_pow_pos s)
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false hlt]

theorem shr3_bne {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 != 0) = decide (8 ≤ n) := by
  rw [bne, VG.Proof.Gcm.AArch64.Pmull.shr3_beq hn]
  by_cases h : n < 8
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

theorem ofNat_bne {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, VG.Proof.Gcm.AArch64.Pmull.ofNat_beq hk]
  by_cases h : k = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true h]; rfl

theorem free_A : VG.Proof.Gcm.AArch64.Pmull.Free A := by unfold VG.Proof.Gcm.AArch64.Pmull.Free; decide

/-! ## The invariant -/

/-- What holds after `i` blocks, with the powers up to `K`. -/
structure Inv (s₀ : State) (K i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  c : s.v C = ofVDwords poly poly
  t : ∀ k, 1 ≤ k → k ≤ K → x * φ (s.v (tReg k)) = φ (H₀ s₀) ^ k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = VG.Proof.Gcm.AArch64.Pmull.ext8 (s.v (tReg k)) (s.v (tReg k))
  y : VG.Proof.Gcm.AArch64.Pmull.ρ (s.v Y) = φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i)
  x0 : s.gpr .x0 = hA s₀
  x1 : s.gpr .x1 = yp s₀
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)
  x5 : s.gpr .x5 = s.gpr .x3 >>> 3
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The invariant does not depend on `x6`. -/
theorem Inv.of_x6 {s₀ : State} {K i : Nat} {s s' : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i s)
    (hg : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i s' where
  le := hI.le
  c := by rw [hv, hI.c]
  t k hk hkK := by rw [hv, hI.t k hk hkK]
  sw k hk hkK := by rw [hv, hI.sw k hk hkK]
  y := by rw [hv, hI.y]
  x0 := by rw [hg .x0 (by decide), hI.x0]
  x1 := by rw [hg .x1 (by decide), hI.x1]
  x2 := by rw [hg .x2 (by decide), hI.x2]
  x3 := by rw [hg .x3 (by decide), hI.x3]
  x5 := by rw [hg .x5 (by decide), hg .x3 (by decide), hI.x5]
  mem := by rw [hm, hI.mem]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

/-! ## The powers -/

theorem nmem_pow {r a b : VReg} (h1 : r ∉ [LO, MID, HI, T]) (h2 : r ≠ a) (h3 : r ≠ b) :
    r ∉ [LO, MID, HI, T, a] ++ [b] := by
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2⟩, h3⟩

theorem tReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    tReg i ≠ tReg j := fun e => h (VG.Proof.Gcm.AArch64.Pmull.tReg_inj i (by omega) j (by omega) hi hj e)

theorem sReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    sReg i ≠ sReg j := fun e => h (VG.Proof.Gcm.AArch64.Pmull.sReg_inj i (by omega) j (by omega) hi hj e)

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`. -/
theorem pow_ok {s₀ : State} {K i j n : Nat} (hi : 1 ≤ i) (hiK : i ≤ K) (hj : 1 ≤ j) (hjK : j ≤ K)
    (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K n s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.pow (K + 1) i j)) s (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ (K + 1) n) := by
  rw [Impl.Gcm.AArch64.Pmull.pow, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.mul_ok (sReg (K + 1)) (sReg i) (sReg j) (tReg j) s (VG.Proof.Gcm.AArch64.Pmull.sReg_free _) (VG.Proof.Gcm.AArch64.Pmull.sReg_free _)
    (VG.Proof.Gcm.AArch64.Pmull.tReg_free _) (hI.sw j hj hjK) hI.c) fun s₁ ⟨m₁, o₁⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.swap_ok (tReg (K + 1)) (sReg (K + 1)) s₁) fun s' ⟨w, o₂⟩ => ?_
  have O := o₁.trans o₂
  have kv : ∀ r, r ∉ [LO, MID, HI, T] → r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r :=
    fun r h1 h2 h3 => O.v r (VG.Proof.Gcm.AArch64.Pmull.nmem_pow h1 h3 h2)
  have ks : s'.v (sReg (K + 1)) = s₁.v (sReg (K + 1)) := o₂.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => VG.Proof.Gcm.AArch64.Pmull.tReg_ne_sReg _ _ e.symm)
  have told : ∀ k, 1 ≤ k → k ≤ K → s'.v (tReg k) = s.v (tReg k) := fun k hk hkK =>
    kv _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' k) (VG.Proof.Gcm.AArch64.Pmull.tReg_ne hk (by omega) (by omega) hK (by omega)) (VG.Proof.Gcm.AArch64.Pmull.tReg_ne_sReg _ _)
  have sold : ∀ k, 1 ≤ k → k ≤ K → s'.v (sReg k) = s.v (sReg k) := fun k hk hkK =>
    kv _ (VG.Proof.Gcm.AArch64.Pmull.sReg_nmem' k) (fun e => VG.Proof.Gcm.AArch64.Pmull.tReg_ne_sReg _ _ e.symm) (VG.Proof.Gcm.AArch64.Pmull.sReg_ne hk (by omega) (by omega) hK (by omega))
  refine ⟨hI.le, by rw [kv C (by decide) (VG.Proof.Gcm.AArch64.Pmull.ne_tReg _) (VG.Proof.Gcm.AArch64.Pmull.ne_sReg _), hI.c],
    fun k hk hkK => ?_, fun k hk hkK => ?_,
    by rw [kv Y (by decide) (VG.Proof.Gcm.AArch64.Pmull.ne_tReg _) (VG.Proof.Gcm.AArch64.Pmull.ne_sReg _), hI.y], by rw [O.gpr, hI.x0],
    by rw [O.gpr, hI.x1], by rw [O.gpr, hI.x2], by rw [O.gpr, hI.x3], by rw [O.gpr, hI.x5],
    by rw [O.mem, hI.mem], by rw [O.rd, hI.rd], by rw [O.wr, hI.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [w, VG.Proof.Gcm.AArch64.Pmull.φ_ext8_self, m₁, hI.sw i hi hiK, VG.Proof.Gcm.AArch64.Pmull.ρ_ext8_self, ← hij, pow_add, ← hI.t i hi hiK,
        ← hI.t j hj hjK]
      ring
    · rw [told k hk hkK', hI.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [ks, w, VG.Proof.Gcm.AArch64.Pmull.ext8_ext8]
    · rw [told k hk hkK', sold k hk hkK', hI.sw k hk hkK']

theorem powers_ok {s₀ : State} {n : Nat} {s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 1 n s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.powers) s (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 n) := by
  simp only [Impl.Gcm.AArch64.Pmull.powers, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 1) (i := 1) (j := 1) le_rfl le_rfl le_rfl le_rfl rfl (by decide) hI)
    fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 2) (i := 2) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 3) (i := 2) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 4) (i := 4) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 5) (i := 4) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 6) (i := 4) (j := 3) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₆) fun s₇ h₇ => ?_
  exact VG.Proof.Gcm.AArch64.Pmull.pow_ok (K := 7) (i := 4) (j := 4) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) h₇

/-! ## The blocks -/

/-- After `j` blocks of `k` from the second on, from `sB`: with the first
block's product, which is added last, the product is `Y` after `j + 1` blocks
times `Hᵏ⁻¹⁻ʲ`. -/
def BI (s₀ sB : State) (k i j : Nat) (s : State) : Prop :=
  (VG.Proof.Gcm.AArch64.Pmull.prod s).val + (φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i) + φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) ^ k =
      φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ (i + 1 + j)) * φ (H₀ s₀) ^ (k - 1 - j) ∧
    VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI, A, T] sB s

theorem blk_ok {s₀ : State} (hp : Pre s₀) {K k i j : Nat} (hkK : k ≤ K) (hK : K ≤ 8)
    (hj : j + 1 < k) (hi : i + k ≤ nb s₀) {sB s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i sB)
    (hB : VG.Proof.Gcm.AArch64.Pmull.BI s₀ sB k i j s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.blk k j)) s (VG.Proof.Gcm.AArch64.Pmull.BI s₀ sB k i (j + 1)) := by
  obtain ⟨hv, o⟩ := hB
  rw [Impl.Gcm.AArch64.Pmull.blk, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.ldrev_ok A .x2 (16 * (j + 1)) s (Nat.mul_mod_right 16 _) (by omega)
    (by rw [o.rd, o.wr, o.gpr, hI.rd, hI.wr, hI.x2]; exact VG.Proof.Gcm.AArch64.Pmull.in_blk16 hp (by omega)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.acc_ok A (sReg (k - 1 - j)) (tReg (k - 1 - j)) s₁ VG.Proof.Gcm.AArch64.Pmull.free_A (VG.Proof.Gcm.AArch64.Pmull.sReg_free _)
    (VG.Proof.Gcm.AArch64.Pmull.tReg_free _)) fun s₂ ⟨p₂, o₂⟩ => ⟨?_, (o.trans (o₁.trans o₂)).weaken⟩
  have o₀₁ := o.trans o₁
  have hs : s₁.v (sReg (k - 1 - j)) = VG.Proof.Gcm.AArch64.Pmull.ext8 (s₁.v (tReg (k - 1 - j))) (s₁.v (tReg (k - 1 - j))) := by
    rw [o₀₁.v _ (VG.Proof.Gcm.AArch64.Pmull.sReg_nmem' _), o₀₁.v _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.sw _ (by omega) (by omega)]
  have ht : x * φ (s₁.v (tReg (k - 1 - j))) = φ (H₀ s₀) ^ (k - 1 - j) := by
    rw [o₀₁.v _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.t _ (by omega) (by omega)]
  have ha : VG.Spec.Gcm.blockAt s.mem (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + 1))) =
      VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ (i + 1 + j)) := by
    rw [o.mem, o.gpr, hI.mem, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add,
      show i + (j + 1) = i + 1 + j by omega]
  have e : φ (H₀ s₀) ^ (k - 1 - j) = φ (H₀ s₀) ^ (k - 1 - (j + 1)) * φ (H₀ s₀) := by
    rw [← pow_succ]; exact congrArg _ (by omega)
  rw [p₂, hs, Prod.val_acc, o₁.prod (by decide) (by decide) (by decide), l₁, ha,
    show i + 1 + (j + 1) = (i + 1 + j) + 1 by omega, VG.Proof.Gcm.AArch64.Pmull.φ_Ys_succ]
  linear_combination hv + (φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ (i + 1 + j)) + φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ (i + 1 + j)))) * e +
    φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ (i + 1 + j))) * ht

theorem body_ok {s₀ : State} (hp : Pre s₀) {K k i : Nat} (hk : 1 ≤ k) (hkK : k ≤ K) (hK : K ≤ 8)
    (hi : i + k ≤ nb s₀) {s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.body k)) s (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K (i + k)) := by
  have hn := hp.nb_lt
  simp only [Impl.Gcm.AArch64.Pmull.body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  have b₀ : VG.Proof.Gcm.AArch64.Pmull.BI s₀ s k i 0 s₁ := by
    refine ⟨?_, o₁.weaken⟩
    have e : φ (H₀ s₀) ^ k = φ (H₀ s₀) ^ (k - 1 - 0) * φ (H₀ s₀) := by
      rw [← pow_succ]; exact congrArg _ (by omega)
    rw [p₁, Prod.val_zero, zero_add, Nat.add_zero, VG.Proof.Gcm.AArch64.Pmull.φ_Ys_succ]
    linear_combination (φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i) + φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ i))) * e
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := k - 1) (VG.Proof.Gcm.AArch64.Pmull.BI s₀ s k i)
    (fun j s' hj hB => VG.Proof.Gcm.AArch64.Pmull.blk_ok hp hkK hK (by omega) hi hI hB) (k - 1) (Nat.le_refl _) s₁ b₀)
    fun s₂ ⟨p₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.ldrev_ok A .x2 (16 * 0) s₂ rfl (by decide)
    (by rw [o₂.rd, o₂.wr, o₂.gpr, hI.rd, hI.wr, hI.x2]; exact VG.Proof.Gcm.AArch64.Pmull.in_blk16 hp (by omega)))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.eor_ok A A Y s₃) fun s₄ ⟨e₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.acc_ok A (sReg k) (tReg k) s₄ VG.Proof.Gcm.AArch64.Pmull.free_A (VG.Proof.Gcm.AArch64.Pmull.sReg_free _) (VG.Proof.Gcm.AArch64.Pmull.tReg_free _))
    fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₂₄ := o₂.trans (o₃.trans o₄)
  have hv : (VG.Proof.Gcm.AArch64.Pmull.prod s₅).val = φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ (i + k)) := by
    have hs : s₄.v (sReg k) = VG.Proof.Gcm.AArch64.Pmull.ext8 (s₄.v (tReg k)) (s₄.v (tReg k)) := by
      rw [o₂₄.v _ (VG.Proof.Gcm.AArch64.Pmull.sReg_nmem' _), o₂₄.v _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.sw _ hk hkK]
    have ht : x * φ (s₄.v (tReg k)) = φ (H₀ s₀) ^ k := by
      rw [o₂₄.v _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.t _ hk hkK]
    have hy : VG.Proof.Gcm.AArch64.Pmull.ρ (s₃.v Y) = φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i) := by
      rw [(o₂.trans o₃).v Y (by decide), hI.y]
    have ha : VG.Spec.Gcm.blockAt s₂.mem (s₂.gpr .x2 + BitVec.ofNat 64 (16 * 0)) =
        VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ i) := by
      rw [o₂.mem, o₂.gpr, hI.mem, hI.x2, Nat.mul_zero, VG.Proof.Gcm.AArch64.Pmull.add_ofNat_zero]
    rw [p₅, hs, Prod.val_acc, (o₃.trans o₄).prod (by decide) (by decide) (by decide), e₄, VG.Proof.Gcm.AArch64.Pmull.ρ_xor,
      l₃, hy, ha]
    have e := p₂
    rw [show i + 1 + (k - 1) = i + k by omega, show k - 1 - (k - 1) = 0 by omega, pow_zero,
      mul_one] at e
    linear_combination e + (φ (VG.Spec.Gcm.blockAt s₀.mem (blkAddr s₀ i)) + φ (VG.Proof.Gcm.AArch64.Pmull.Ys s₀ i)) * ht
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.reduce_ok Y s₅ (by rw [(o₂₄.trans o₅).v C (by decide), hI.c]))
    fun s₆ ⟨r₆, o₆⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.advance_ok k (by omega) s₆)
    fun s' ⟨f2, f3, f5, fg, fv, fm, frd, fwr⟩ => ?_
  have O : VG.Proof.Gcm.AArch64.Pmull.VOnly [LO, MID, HI, A, T, Y] s s₆ :=
    (o₂.trans ((o₃.trans (o₄.trans o₅)).trans o₆)).weaken
  have kv : ∀ r, r ∉ [LO, MID, HI, A, T, Y] → s'.v r = s.v r := fun r h => by rw [fv, O.v r h]
  have kg : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r := fun r h2 h3 h5 => by
    rw [fg r h2 h3 h5, O.gpr]
  refine ⟨by omega, by rw [kv C (by decide), hI.c],
    fun m hm hmK => by rw [kv _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.t m hm hmK],
    fun m hm hmK => by rw [kv _ (VG.Proof.Gcm.AArch64.Pmull.sReg_nmem' _), kv _ (VG.Proof.Gcm.AArch64.Pmull.tReg_nmem' _), hI.sw m hm hmK], ?_,
    by rw [kg .x0 (by decide) (by decide) (by decide), hI.x0],
    by rw [kg .x1 (by decide) (by decide) (by decide), hI.x1], ?_, ?_, f5,
    by rw [fm, O.mem, hI.mem], by rw [frd, O.rd, hI.rd], by rw [fwr, O.wr, hI.wr]⟩
  · rw [fv, r₆, VG.Proof.Gcm.AArch64.Pmull.ρ_reduce, hv]
  · rw [f2, O.gpr, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]
  · rw [f3, O.gpr, hI.x3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

/-! ## The prologue and the epilogue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologue) s₀ (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 1 0) := by
  simp only [Impl.Gcm.AArch64.Pmull.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.ldrev_ok A .x0 0 s₀ rfl (by decide)
    ⟨hR s₀, by simp [hp.rd], contains_offset (by decide) (by decide)⟩) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.consts_ok s₁) fun s₂ ⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.mul_ok (sReg 1) A (sReg 2) (tReg 2) s₂ VG.Proof.Gcm.AArch64.Pmull.free_A (VG.Proof.Gcm.AArch64.Pmull.sReg_free _) (VG.Proof.Gcm.AArch64.Pmull.tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have g₄ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s₄.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  have mem₄ : s₄.mem = s₀.mem := by rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.ldrev_ok Y .x1 0 s₄ rfl (by decide)
    (by rw [o₄.rd, o₄.wr, o₃.rd, o₃.wr, rd₂, wr₂, o₁.rd, o₁.wr,
      g₄ .x1 (by decide) (by decide) (by decide)]
        exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩))
    fun s₅ ⟨l₅, o₅⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.lsr_ok .x5 .x3 3 (by decide) s₅) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [fg r h5, o₅.gpr, g₄ r h5 h6 h7]
  have O : VG.Proof.Gcm.AArch64.Pmull.VOnly ([tReg 1] ++ [Y]) s₃ s₅ := o₄.trans o₅
  have t₁ : s'.v (tReg 1) = VG.Proof.Gcm.AArch64.Pmull.ext8 (s₃.v (sReg 1)) (s₃.v (sReg 1)) := by
    rw [fv, o₅.v _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact (VG.Proof.Gcm.AArch64.Pmull.ne_tReg (r := Y) 1).symm), w₄]
  have s₁' : s'.v (sReg 1) = s₃.v (sReg 1) := by
    rw [fv, O.v _ (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => VG.Proof.Gcm.AArch64.Pmull.tReg_ne_sReg _ _ e.symm, (VG.Proof.Gcm.AArch64.Pmull.ne_sReg (r := Y) 1).symm⟩)]
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (VG.Proof.Gcm.AArch64.Pmull.ne_tReg 2) (VG.Proof.Gcm.AArch64.Pmull.ne_sReg 2)
  refine ⟨Nat.zero_le _, ?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_, ?_,
    by rw [g .x0 (by decide) (by decide) (by decide)],
    by rw [g .x1 (by decide) (by decide) (by decide)],
    by rw [g .x2 (by decide) (by decide) (by decide)]; simp [blkAddr],
    by rw [g .x3 (by decide) (by decide) (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₅.mem, mem₄],
    by rw [frd, o₅.rd, o₄.rd, o₃.rd, rd₂, o₁.rd], by rw [fwr, o₅.wr, o₄.wr, o₃.wr, wr₂, o₁.wr]⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, VG.Proof.Gcm.AArch64.Pmull.ne_sReg 1⟩
    have h' : C ∉ [tReg 1] ++ [Y] := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨VG.Proof.Gcm.AArch64.Pmull.ne_tReg 1, by decide⟩
    rw [fv, O.v C h', o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega
    rw [t₁, VG.Proof.Gcm.AArch64.Pmull.φ_ext8_self, m₃, hA₂, l₁, t₂, VG.Proof.Gcm.AArch64.Pmull.add_ofNat_zero]
    linear_combination φ (H₀ s₀) * VG.Proof.Gcm.AArch64.Pmull.x2_φ_xInv2
  · obtain rfl : k = 1 := by omega
    rw [t₁, s₁', VG.Proof.Gcm.AArch64.Pmull.ext8_ext8]
  · rw [fv, l₅, mem₄, g₄ .x1 (by decide) (by decide) (by decide), VG.Proof.Gcm.AArch64.Pmull.add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {K : Nat} {s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K (nb s₀) s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.epilogue) s fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_strq (s := s.setV Y _) (by decide) (by decide) hout,
    WP.block_nil ?_⟩
  show VG.Spec.Gcm.blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x1 + BitVec.ofNat 64 0) 16
    ((s.setV Y _).v Y)) (yp s₀) = VG.Proof.Gcm.AArch64.Pmull.Ys s₀ (nb s₀)
  apply φ_inj
  simp only [VG.Proof.Gcm.AArch64.Pmull.mem_setV, VG.Proof.Gcm.AArch64.Pmull.gpr_setV, VG.Proof.Gcm.AArch64.Pmull.v_setV, ↓reduceIte, hI.x1, VG.Proof.Gcm.AArch64.Pmull.add_ofNat_zero, VG.Proof.Gcm.AArch64.Pmull.φ_store, hI.y]

/-! ## The whole function -/

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun s' => WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h
  exact WP.seq (WP.mono h fun _ h' => WP.seq h')

/-- The remaining blocks, one at a time. -/
theorem ones_ok {s₀ : State} (hp : Pre s₀) {K i : Nat} (hK1 : 1 ≤ K) (hK8 : K ≤ 8) {s : State}
    (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i s) :
    WP isa (.ite (.zero .x .x3) (.block [])
      (.loop (.block (Impl.Gcm.AArch64.Pmull.body 1)) (.nonzero .x .x3))) s (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x3) s = some (decide (nb s₀ - i = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI.x3,
      VG.Proof.Gcm.AArch64.Pmull.ofNat_beq (show nb s₀ - i < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i = nb s₀ := by have := hI.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI)
  · let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 1)) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.body_ok hp le_rfl hK1 hK8 (by omega) hI) fun s' hI' => ?_
      have hev : eval (.nonzero .x .x3) s' = some (decide (nb s₀ - (i + 1) ≠ 0)) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x3,
          VG.Proof.Gcm.AArch64.Pmull.ofNat_bne (show nb s₀ - (i + 1) < 2 ^ 64 by omega)]
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by rw [hev, decide_eq_false (not_not.mpr hlast)], this ▸ hI'⟩
      · exact .inr ⟨by rw [hev, decide_eq_true hlast], nb s₀ - (i + 1), by omega, i + 1, rfl,
          by omega, hI'⟩
    have hlt : i < nb s₀ := by have := hI.le; simp only [decide_eq_false_iff_not] at h; omega
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s ⟨i, rfl, hlt, hI⟩

/-- `k` blocks if bit `sh` of the remaining count (less than `2 ^ (sh + 1)`) is
set, with `k = 2 ^ sh`. -/
theorem bit_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (sh k : Nat) (hk : k = 2 ^ sh) (hk1 : 1 ≤ k)
    (hk8 : k ≤ 8) (hsh : sh < 64) (hi : nb s₀ - i < 2 * k) {s : State} (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i s) :
    WP isa (.seq (.block [.lsr .x .x6 .x3 sh])
      (.ite (.zero .x .x6) (.block []) (.block (Impl.Gcm.AArch64.Pmull.body k)))) s
      (fun s' => ∃ i', nb s₀ - i' < k ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i' s') := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (VG.Proof.Gcm.AArch64.Pmull.lsr_ok .x6 .x3 sh hsh s) fun s₁ ⟨f6, fg, fv, fm, frd, fwr⟩ => ?_)
  have hI₁ := hI.of_x6 fg fv fm frd fwr
  have hev : eval (.zero .x .x6) s₁ = some (decide (nb s₀ - i < k)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, f6, hI.x3,
      VG.Proof.Gcm.AArch64.Pmull.shr_beq sh (show nb s₀ - i < 2 ^ 64 by omega), hk]
  refine WP.ite _ hev (fun h => WP.block_nil ⟨i, by simpa using h, hI₁⟩) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact WP.mono (VG.Proof.Gcm.AArch64.Pmull.body_ok hp hk1 hk8 le_rfl (by omega) hI₁) fun s' h' => ⟨i + k, by omega, h'⟩

/-- The last `n mod 8` blocks, once the powers are computed. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : nb s₀ - i < 8) {s : State}
    (hI : VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i s) :
    WP isa Impl.Gcm.AArch64.Pmull.tail s (VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  unfold Impl.Gcm.AArch64.Pmull.tail
  refine WP.seq_assoc (WP.mono (VG.Proof.Gcm.AArch64.Pmull.bit_ok hp 2 4 rfl (by decide) (by decide) (by decide) (by omega) hI)
    fun s₁ ⟨i₁, hi₁, hI₁⟩ => ?_)
  refine WP.seq_assoc (WP.mono (VG.Proof.Gcm.AArch64.Pmull.bit_ok hp 1 2 rfl (by decide) (by decide) (by decide) (by omega)
    hI₁) fun s₂ ⟨i₂, hi₂, hI₂⟩ => ?_)
  have hev : eval (.zero .x .x3) s₂ = some (decide (nb s₀ - i₂ = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₂.x3,
      VG.Proof.Gcm.AArch64.Pmull.ofNat_beq (show nb s₀ - i₂ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i₂ = nb s₀ := by have := hI₂.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · simp only [decide_eq_false_iff_not] at h
    have : i₂ + 1 = nb s₀ := by omega
    exact this ▸ VG.Proof.Gcm.AArch64.Pmull.body_ok hp le_rfl (by decide) le_rfl (by omega) hI₂

theorem loops_ok {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (VG.Proof.Gcm.AArch64.Pmull.prologue_ok hp) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ K, VG.Proof.Gcm.AArch64.Pmull.Inv s₀ K (nb s₀) s) ?_
    fun s₂ ⟨K, hI₂⟩ => VG.Proof.Gcm.AArch64.Pmull.epilogue_ok hp hI₂)
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      VG.Proof.Gcm.AArch64.Pmull.shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => WP.mono (VG.Proof.Gcm.AArch64.Pmull.ones_ok hp le_rfl (by decide) hI₁) fun s h => ⟨1, h⟩)
    (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  refine WP.seq (WP.mono (VG.Proof.Gcm.AArch64.Pmull.powers_ok hI₁) fun s₃ hI₃ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => WP.mono (VG.Proof.Gcm.AArch64.Pmull.tail_ok hp hi hI₄) fun s h => ⟨8, h⟩)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ VG.Proof.Gcm.AArch64.Pmull.Inv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.Gcm.AArch64.Pmull.body_ok hp (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        VG.Proof.Gcm.AArch64.Pmull.shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₃ ⟨0, rfl, by omega, hI₃⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (VG.Proof.Gcm.AArch64.Pmull.loops_ok hp) (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Gcm.AArch64.Pmull.correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ghash_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghash (Spec.Gcm.ghashContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Gcm.AArch64.Pmull.ghash_correct VG.Proof.Gcm.AArch64.Pmull.ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

end VG.Proof.Gcm.AArch64.Pmull

end
