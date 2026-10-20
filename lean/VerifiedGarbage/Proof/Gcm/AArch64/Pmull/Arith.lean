module

public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ops
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

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

@[expose] public section

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
    gp (clSteps a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (63 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [clSteps, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : clSteps a b (k + 1) =
        if a.getLsbD k then clSteps a b k ^^^ (b.setWidth 128 <<< k) else clSteps a b k := by
      simp only [clSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega), gp_shl b (by omega),
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
  rw [show polyMul a b = clSteps a b 64 from rfl, gp_clSteps a b (Nat.le_refl _), gp_lsb]

/-! ## Doublewords -/

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem φ_polyMul (a b : BitVec 64) : φ (polyMul a b) = x * ψ a * ψ b := by
  simp only [φ, ψ, gp_polyMul, map_mul, AdjoinRoot.mk_X]

theorem ψ_xor (a b : BitVec 64) : ψ (a ^^^ b) = ψ a + ψ b := by
  simp only [ψ, gp_xor, map_add]

theorem φ_append (a b : BitVec 64) : φ (a ++ b) = ψ a + x ^ 64 * ψ b := by
  simp only [φ, ψ, gp_append, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

theorem φ_v (v : BitVec 128) : φ v = ψ (vdword v 1) + x ^ 64 * ψ (vdword v 0) := by
  conv => lhs; rw [vdwords v]
  rw [φ_append]

/-- The class of a block as loaded (its halves swapped). -/
noncomputable def ρ (v : BitVec 128) : Q := ψ (vdword v 0) + x ^ 64 * ψ (vdword v 1)

theorem ρ_xor (a b : BitVec 128) : ρ (a ^^^ b) = ρ a + ρ b := by
  simp only [ρ, vdword_xor, ψ_xor]; ring

theorem φ_ext8 (n m : BitVec 128) : φ (ext8 n m) = ψ (vdword m 0) + x ^ 64 * ψ (vdword n 1) := by
  rw [ext8_eq, φ_append]

/-- A block with its halves swapped, as loaded. -/
theorem ρ_ext8_self (v : BitVec 128) : ρ (ext8 v v) = φ v := by
  rw [ρ, vdword_ext8_0, vdword_ext8_1, φ_v]

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

theorem val_zero : zero.val = 0 := by
  simp only [val, zero, BitVec.ofNat_eq_ofNat, φ_zero', mul_zero, add_zero]

theorem val_acc (p : Prod) (a t : BitVec 128) :
    (p.acc a (ext8 t t) t).val = p.val + x * ρ a * φ t := by
  simp only [acc, val, φ_xor, vdword_ext8_0, vdword_ext8_1, φ_polyMul, ρ, φ_v t]
  ring

end Prod

/-! ## The reduction -/

theorem ψ_poly : ψ poly = 1 + x + x ^ 6 := by
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
      · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte,
          show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : poly.getMsbD d = false := by
        simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
        omega
      rw [e]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega,
        show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega]
  simp only [ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem φ_ext8_self (v : BitVec 128) : φ (ext8 v v) = ρ v := by rw [φ_ext8, ρ]

/-- A block as loaded, plus the `pmull` of its low half by `0xc2 · 2⁵⁶`, is of
the class of `x⁶⁴` times the block. -/
theorem ρ_add_polyMul (u : BitVec 128) : ρ u + φ (polyMul (vdword u 0) poly) = x ^ 64 * φ u := by
  rw [ρ, φ_polyMul, ψ_poly, φ_v u]
  linear_combination (-ψ (vdword u 0)) * x128

/-- `fold(v) = swap(v) ⊕ pmull(v₀, 0xc2 · 2⁵⁶)` is of the class of `x⁶⁴ · v`. -/
theorem φ_fold (v : BitVec 128) : φ (ext8 v v ^^^ polyMul (vdword v 0) poly) = x ^ 64 * φ v := by
  rw [φ_xor, φ_ext8_self, ρ_add_polyMul]

theorem ρ_reduce (p : Prod) : ρ (reduce p) = p.val := by
  simp only [reduce]
  rw [ρ_xor, ρ_xor, ρ_ext8_self, ρ_ext8_self, add_assoc, ρ_add_polyMul, BitVec.xor_assoc, φ_xor,
    φ_fold, Prod.val]
  ring

/-! ## `x⁻²` -/

theorem gp_xInv2 : gp xInv2 = X + X ^ 5 + X ^ 6 + X ^ 126 + X ^ 127 := by
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
    · simp only [bit, h1, decide_false, h5, Bool.or_self, h6, h126, h127, Bool.false_eq_true,
        ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv2.getMsbD d = false := by
      simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d by omega, add_zero,
      show d ≠ 5 by omega, show d ≠ 6 by omega, show d ≠ 126 by omega, show d ≠ 127 by omega]

theorem x2_φ_xInv2 : x ^ 2 * φ xInv2 = 1 := by
  simp only [φ, gp_xInv2, map_add, map_pow, AdjoinRoot.mk_X]
  linear_combination (1 + x) * x128 + (x + x ^ 2 + x ^ 3 + x ^ 7 + x ^ 8) * two_Q

end VG.Proof.Gcm.AArch64.Pmull
