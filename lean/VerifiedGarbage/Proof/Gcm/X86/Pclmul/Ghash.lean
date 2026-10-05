import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Impl.Gcm.X86.Pclmul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.X86.Ghash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Arith`. -/
section

section

section

/-!
# GHASH with PCLMULQDQ: the arithmetic

Untrusted: everything here is checked by Lean. What the instructions of
`Impl.Gcm.X86.Pclmul` compute, in the ring `Q` of `Proof/Gcm/Poly.lean`:

* `pclmulqdq` multiplies polynomials (`gp_clmul`), so the four of `acc`
  compute `x · a · b` as a 256-bit value (`Prod.val_prod`);
* `reduce` maps a 256-bit value to a block of the same class
  (`φ_reduce`);
* `hInv` computes `H · x⁻¹` (`x_φ_hInv`).
-/

namespace VG.Proof.Gcm.X86.Pclmul

open Polynomial
open VG.X86 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86.Pclmul (poly xInv)

/-! ## Carry-less multiplication -/

theorem gp_shl (b : BitVec 64) {j : Nat} (hj : j < 64) :
    gp ((b.setWidth 128) <<< j) = X ^ (64 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 64 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 128 - 64 ≤ d + j by omega), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [h, ite_false, decide_eq_false (show ¬ 128 - 64 ≤ d + j by omega), Bool.false_and]; rfl

/-- The first `k` steps of `clmul`. -/
def clSteps (a b : BitVec 64) (k : Nat) : BitVec 128 :=
  (List.range k).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

theorem gp_clSteps (a b : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    gp (VG.Proof.Gcm.X86.Pclmul.clSteps a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (63 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [VG.Proof.Gcm.X86.Pclmul.clSteps, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : VG.Proof.Gcm.X86.Pclmul.clSteps a b (k + 1) =
        if a.getLsbD k then VG.Proof.Gcm.X86.Pclmul.clSteps a b k ^^^ (b.setWidth 128 <<< k) else VG.Proof.Gcm.X86.Pclmul.clSteps a b k := by
      simp only [VG.Proof.Gcm.X86.Pclmul.clSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega), VG.Proof.Gcm.X86.Pclmul.gp_shl b (by omega),
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

/-- `pclmulqdq` multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_clmul (a b : BitVec 64) : gp (clmul a b) = X * gp a * gp b := by
  rw [show clmul a b = VG.Proof.Gcm.X86.Pclmul.clSteps a b 64 from rfl, VG.Proof.Gcm.X86.Pclmul.gp_clSteps a b (Nat.le_refl _), VG.Proof.Gcm.X86.Pclmul.gp_lsb]

/-! ## Quadwords -/

theorem qwords (v : BitVec 128) : v = qword v 1 ++ qword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, mul_zero, zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem gp_qwords (v : BitVec 128) : gp v = gp (qword v 1) + X ^ 64 * gp (qword v 0) := by
  conv => lhs; rw [VG.Proof.Gcm.X86.Pclmul.qwords v]
  rw [gp_append]

theorem φ_qwords (v : BitVec 128) :
    φ v = AdjoinRoot.mk g (gp (qword v 1)) + VG.Proof.Gcm.Poly.x ^ 64 * AdjoinRoot.mk g (gp (qword v 0)) := by
  rw [φ, VG.Proof.Gcm.X86.Pclmul.gp_qwords]; simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X]

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : VG.Proof.Gcm.Poly.Q := AdjoinRoot.mk g (gp q)

theorem φ_clmul (a b : BitVec 64) : φ (clmul a b) = VG.Proof.Gcm.Poly.x * VG.Proof.Gcm.X86.Pclmul.ψ a * VG.Proof.Gcm.X86.Pclmul.ψ b := by
  simp only [φ, VG.Proof.Gcm.X86.Pclmul.ψ, VG.Proof.Gcm.X86.Pclmul.gp_clmul, map_mul, AdjoinRoot.mk_X]

theorem φ_q (v : BitVec 128) : φ v = VG.Proof.Gcm.X86.Pclmul.ψ (qword v 1) + VG.Proof.Gcm.Poly.x ^ 64 * VG.Proof.Gcm.X86.Pclmul.ψ (qword v 0) := VG.Proof.Gcm.X86.Pclmul.φ_qwords v

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : VG.Proof.Gcm.X86.Pclmul.Prod) : VG.Proof.Gcm.Poly.Q := φ p.hi + VG.Proof.Gcm.Poly.x ^ 64 * φ p.mid + VG.Proof.Gcm.Poly.x ^ 128 * φ p.lo

def xor (p q : VG.Proof.Gcm.X86.Pclmul.Prod) : VG.Proof.Gcm.X86.Pclmul.Prod := ⟨p.lo ^^^ q.lo, p.mid ^^^ q.mid, p.hi ^^^ q.hi⟩

/-- The four products of `acc`, added to `p`. -/
def acc (p : VG.Proof.Gcm.X86.Pclmul.Prod) (a b : BitVec 128) : VG.Proof.Gcm.X86.Pclmul.Prod :=
  ⟨p.lo ^^^ pclmul a b 0x00,
   p.mid ^^^ pclmul a b 0x01 ^^^ pclmul a b 0x10,
   p.hi ^^^ pclmul a b 0x11⟩

def zero : VG.Proof.Gcm.X86.Pclmul.Prod := ⟨0, 0, 0⟩

theorem val_zero : zero.val = 0 := by simp only [VG.Proof.Gcm.X86.Pclmul.Prod.val, VG.Proof.Gcm.X86.Pclmul.Prod.zero, BitVec.ofNat_eq_ofNat, φ_zero', mul_zero, add_zero]

theorem val_acc (p : VG.Proof.Gcm.X86.Pclmul.Prod) (a b : BitVec 128) : (p.acc a b).val = p.val + VG.Proof.Gcm.Poly.x * φ a * φ b := by
  simp only [VG.Proof.Gcm.X86.Pclmul.Prod.acc, VG.Proof.Gcm.X86.Pclmul.Prod.val, φ_xor]
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x01 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x01 : BitVec 8).getLsbD 4 = false from rfl, show (0x10 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x10 : BitVec 8).getLsbD 4 = true from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    VG.Proof.Gcm.X86.Pclmul.φ_clmul, VG.Proof.Gcm.X86.Pclmul.φ_q a, VG.Proof.Gcm.X86.Pclmul.φ_q b]
  ring

end Prod

/-! ## The reduction -/

theorem shr64 (v : BitVec 128) : v >>> 64 = 0#64 ++ qword v 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · simp only [h, ite_false, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem shl64 (v : BitVec 128) : v <<< 64 = qword v 0 ++ 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  by_cases h : i < 64
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, ↓reduceIte, BitVec.getLsbD_eq_getElem, BitVec.getElem_zero]
  · simp only [h, ite_false, decide_false, Bool.not_false, Bool.true_and, Nat.mul_zero, Nat.zero_add,
      decide_eq_true (show i - 64 < 64 by omega), decide_eq_true hi, Bool.and_true]

theorem φ_shr64 (v : BitVec 128) : φ (v >>> 64) = VG.Proof.Gcm.Poly.x ^ 64 * VG.Proof.Gcm.X86.Pclmul.ψ (qword v 1) := by
  rw [φ, VG.Proof.Gcm.X86.Pclmul.shr64, gp_append, gp_zero']; simp only [zero_add, map_mul, map_pow, AdjoinRoot.mk_X, VG.Proof.Gcm.X86.Pclmul.ψ]

theorem φ_shl64 (v : BitVec 128) : φ (v <<< 64) = VG.Proof.Gcm.X86.Pclmul.ψ (qword v 0) := by
  rw [φ, VG.Proof.Gcm.X86.Pclmul.shl64, gp_append, gp_zero']; simp only [mul_zero, add_zero, VG.Proof.Gcm.X86.Pclmul.ψ]

theorem ψ_c : VG.Proof.Gcm.X86.Pclmul.ψ (qword poly 1) = 1 + VG.Proof.Gcm.Poly.x + VG.Proof.Gcm.Poly.x ^ 6 := by
  have hb : ∀ d < 64, (qword poly 1).getMsbD d = (d = 0 || d = 1 || d = 6) := by decide +kernel
  have h : gp (qword poly 1) = 1 + X + X ^ 6 := by
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
      · simp only [VG.Proof.Gcm.Poly.bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : (qword poly 1).getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
      rw [e]
      simp only [VG.Proof.Gcm.Poly.bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega, show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega]
  simp only [VG.Proof.Gcm.X86.Pclmul.ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem shufDwords_4e (a : BitVec 128) : shufDwords a 0x4e = qword a 0 ++ qword a 1 := by
  rw [show shufDwords a 0x4e = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_ofDwords, getLsbD_dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega)

/-- One step of the reduction: `swap(v) ⊕ clmul(v₀, c)`. -/
def fold (v : BitVec 128) : BitVec 128 := shufDwords v 0x4e ^^^ pclmul v poly 0x10

theorem φ_fold (v : BitVec 128) : φ (VG.Proof.Gcm.X86.Pclmul.fold v) = VG.Proof.Gcm.Poly.x ^ 64 * φ v := by
  have e1 : φ (shufDwords v 0x4e) = VG.Proof.Gcm.X86.Pclmul.ψ (qword v 0) + VG.Proof.Gcm.Poly.x ^ 64 * VG.Proof.Gcm.X86.Pclmul.ψ (qword v 1) := by
    rw [VG.Proof.Gcm.X86.Pclmul.shufDwords_4e, φ, gp_append]; simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, VG.Proof.Gcm.X86.Pclmul.ψ]
  have e2 : pclmul v poly 0x10 = clmul (qword v 0) (qword poly 1) := rfl
  rw [VG.Proof.Gcm.X86.Pclmul.fold, φ_xor, e1, e2, VG.Proof.Gcm.X86.Pclmul.φ_clmul, VG.Proof.Gcm.X86.Pclmul.ψ_c, VG.Proof.Gcm.X86.Pclmul.φ_q v]
  linear_combination (-VG.Proof.Gcm.X86.Pclmul.ψ (qword v 0)) * x128

/-- The block `reduce` computes from a product. -/
def reduce (p : VG.Proof.Gcm.X86.Pclmul.Prod) : BitVec 128 :=
  (p.hi ^^^ p.mid >>> 64) ^^^ VG.Proof.Gcm.X86.Pclmul.fold (VG.Proof.Gcm.X86.Pclmul.fold (p.lo ^^^ p.mid <<< 64))

theorem φ_reduce (p : VG.Proof.Gcm.X86.Pclmul.Prod) : φ (VG.Proof.Gcm.X86.Pclmul.reduce p) = p.val := by
  simp only [VG.Proof.Gcm.X86.Pclmul.reduce, φ_xor, VG.Proof.Gcm.X86.Pclmul.φ_fold, VG.Proof.Gcm.X86.Pclmul.φ_shr64, VG.Proof.Gcm.X86.Pclmul.φ_shl64, Prod.val, VG.Proof.Gcm.X86.Pclmul.φ_q p.mid]
  ring

/-! ## `H · x⁻¹` -/

theorem shl1 (h : BitVec 128) :
    XShiftOp.eval .psllq h 1 ||| XShiftOp.eval .pslldq (XShiftOp.eval .psrlq h 63) 8 = h <<< 1 := by
  have e1 : XShiftOp.eval .psllq h 1 = (qword h 1 <<< 1) ++ (qword h 0 <<< 1) := rfl
  have e2 : XShiftOp.eval .psrlq h 63 = (qword h 1 >>> 63) ++ (qword h 0 >>> 63) := rfl
  have e3 : ∀ y, XShiftOp.eval .pslldq y 8 = y <<< 64 := fun _ => rfl
  rw [e1, e2, e3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, qword, BitVec.getLsbD_extractLsb']
  rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i < 64) ∨ i = 64 ∨ 64 < i) with h | h | h | h
  · subst h; simp only [Nat.ofNat_pos, ↓reduceIte, decide_true, Order.lt_one_iff, Bool.not_true, Bool.and_false, zero_tsub, mul_zero, add_zero, BitVec.getLsbD_eq_getElem, Bool.true_and, Bool.false_and, Nat.lt_add_one, zero_add, Nat.reduceLT, Bool.or_self]
  · simp (disch := omega) only [ite_eq_left, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true, Bool.not_true]
    exact congrArg _ (by omega)
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true,
      Bool.not_true]
    exact congrArg _ (by omega)

theorem shr31 (y : BitVec 32) : y >>> 31 = if y.msb then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  have := y.isLt
  split_ifs with h
  · simp only [Nat.add_one_sub_one, Nat.reducePow, decide_eq_true_eq] at h; simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat, Nat.one_mod]; omega
  · simp only [Nat.add_one_sub_one, Nat.reducePow, decide_eq_true_eq, not_le] at h; simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat, Nat.zero_mod, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, gt_iff_lt]; omega

theorem msb_dword3 (h : BitVec 128) : dword h 3 >>> 31 = if h.getMsbD 0 then 1#32 else 0#32 := by
  have e : (dword h 3).msb = h.getMsbD 0 := by
    simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword, BitVec.getMsbD]; rfl
  rw [VG.Proof.Gcm.X86.Pclmul.shr31, e]

/-- The mask of `hInv`: `x⁻¹` if the bit shifted out of `h` is 1, else 0. -/
theorem mask_eq (h : BitVec 128) :
    XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld (shufDwords h 0xff) 31)
      (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
        ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)))) xInv =
      if h.getMsbD 0 then xInv else 0 := by
  have e0 : shufDwords h 0xff = ofDwords (dword h 3) (dword h 3) (dword h 3) (dword h 3) := rfl
  have e1 : ∀ a, XShiftOp.eval .psrld a 31 =
      ofDwords (dword a 0 >>> 31) (dword a 1 >>> 31) (dword a 2 >>> 31) (dword a 3 >>> 31) :=
    fun _ => rfl
  have e2 : XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
      ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) = ofDwords (-1) (-1) (-1) (-1) := by rfl
  rw [e0, e1, e2]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, VG.Proof.Gcm.X86.Pclmul.msb_dword3]
  split_ifs
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (1#32 : BitVec 32) + -1 = 0 by rfl, show ofDwords 0 0 0 0 = 0 by rfl]
    rfl
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (0#32 : BitVec 32) + -1 = -1 by rfl,
      show ~~~ofDwords (-1) (-1) (-1) (-1) = 0 by rfl]
    rfl

theorem gp_xInv : gp xInv = 1 + X + X ^ 6 + X ^ 127 := by
  have hb : ∀ d < 128, xInv.getMsbD d = (d = 0 || d = 1 || d = 6 || d = 127) := by decide +kernel
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 127 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h6, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp only [VG.Proof.Gcm.Poly.bit, h0, decide_false, h1, Bool.or_self, h6, h7, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv.getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
    rw [e]
    simp only [VG.Proof.Gcm.Poly.bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega, show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega, show d ≠ 127 by omega]

theorem x_φ_xInv : VG.Proof.Gcm.Poly.x * φ xInv = 1 := by
  simp only [φ, VG.Proof.Gcm.X86.Pclmul.gp_xInv, map_add, map_one, map_pow, AdjoinRoot.mk_X]
  linear_combination x128 + (VG.Proof.Gcm.Poly.x + VG.Proof.Gcm.Poly.x ^ 2 + VG.Proof.Gcm.Poly.x ^ 7) * two_Q

theorem gp_shl1 (h : BitVec 128) : X * gp (h <<< 1) + C (VG.Proof.Gcm.Poly.bit (h.getMsbD 0)) = gp h := by
  ext d
  rw [coeff_add, coeff_C, coeff_gp]
  rcases d with _ | d
  · simp only [mul_coeff_zero, coeff_X_zero, zero_mul, ↓reduceIte, zero_add]
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]; simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]

/-- `hInv`'s result is `H · x⁻¹`. -/
theorem x_φ_hInv (h : BitVec 128) :
    VG.Proof.Gcm.Poly.x * φ ((h <<< 1) ^^^ (if h.getMsbD 0 then xInv else 0)) = φ h := by
  have e := congrArg (AdjoinRoot.mk g) (VG.Proof.Gcm.X86.Pclmul.gp_shl1 h)
  simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at e
  rw [φ_xor, mul_add]
  change VG.Proof.Gcm.Poly.x * AdjoinRoot.mk g (gp (h <<< 1)) + _ = AdjoinRoot.mk g (gp h)
  rw [← e]
  split_ifs with hb
  · rw [VG.Proof.Gcm.X86.Pclmul.x_φ_xInv, hb]; simp only [VG.Proof.Gcm.Poly.bit, ↓reduceIte, map_one]
  · rw [φ_zero, Bool.not_eq_true] at *; rw [hb]; simp only [mul_zero, add_zero, VG.Proof.Gcm.Poly.bit, Bool.false_eq_true, ↓reduceIte, map_zero]

end VG.Proof.Gcm.X86.Pclmul

end


end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash`. -/
section

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Const`.
section

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86.Pclmul (at_ poly xInv)

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := rfl

theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< 64 := rfl

theorem rev_eq : Impl.Gcm.X86.Pclmul.revMask = VG.Proof.Gcm.X86.revMask := rfl

/-- `s'` differs from `s` at most in the SSE registers `rs`. -/
structure Only (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem Only.trans {rs rs' : List XReg} {s s' s'' : State} (h : VG.Proof.Gcm.X86.Pclmul.Only rs s s') (h' : VG.Proof.Gcm.X86.Pclmul.Only rs' s' s'') :
    VG.Proof.Gcm.X86.Pclmul.Only (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Only.weaken {rs rs' : List XReg} {s s' : State} (h : VG.Proof.Gcm.X86.Pclmul.Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Gcm.X86.Pclmul.Only rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- The product registers. -/
def prod (s : State) : VG.Proof.Gcm.X86.Pclmul.Prod := ⟨s.xmm .xmm4, s.xmm .xmm5, s.xmm .xmm6⟩

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.zero) s fun s' =>
      VG.Proof.Gcm.X86.Pclmul.prod s' = Prod.zero ∧ VG.Proof.Gcm.X86.Pclmul.Only [.xmm4, .xmm5, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.zero]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, xmm_setXmm, VG.Proof.Gcm.X86.Pclmul.eval_pxor, BitVec.xor_self, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.acc) s fun s' =>
      VG.Proof.Gcm.X86.Pclmul.prod s' = (VG.Proof.Gcm.X86.Pclmul.prod s).acc (s.xmm .xmm2) (s.xmm .xmm3) ∧
      VG.Proof.Gcm.X86.Pclmul.Only [.xmm4, .xmm5, .xmm6, .xmm7] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.acc]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    VG.Proof.Gcm.X86.Pclmul.eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [VG.Proof.Gcm.X86.Pclmul.prod, Prod.acc, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.reduce) s fun s' =>
      s'.xmm .xmm2 = VG.Proof.Gcm.X86.Pclmul.reduce (VG.Proof.Gcm.X86.Pclmul.prod s) ∧ VG.Proof.Gcm.X86.Pclmul.Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.reduce, Impl.Gcm.X86.Pclmul.fold,
    List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    VG.Proof.Gcm.X86.Pclmul.eval_pxor, eval_movdqa, h1, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [VG.Proof.Gcm.X86.Pclmul.prod, VG.Proof.Gcm.X86.Pclmul.psrldq8, VG.Proof.Gcm.X86.Pclmul.pslldq8]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Multiply the accumulator by the transformed hash key. -/
theorem mul_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.zero ++ Impl.Gcm.X86.Pclmul.acc ++
      Impl.Gcm.X86.Pclmul.reduce)) s fun s' =>
      φ (s'.xmm .xmm2) = VG.Proof.Gcm.Poly.x * φ (s.xmm .xmm2) * φ (s.xmm .xmm3) ∧
      VG.Proof.Gcm.X86.Pclmul.Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.acc_ok s₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by
    rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.reduce_ok s₂ e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, VG.Proof.Gcm.X86.Pclmul.φ_reduce, p₂, p₁, Prod.val_acc, Prod.val_zero, zero_add,
      o₁.xmm .xmm2 (by decide), o₁.xmm .xmm3 (by decide)]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly

/-- Append a low dword to the lower ninety-six bits of the previous value. -/
def catWord (v : BitVec 128) (d : BitVec 32) : BitVec 128 :=
  (v <<< 32) ||| ((0 : BitVec 96) ++ d)

def assembled (c : BitVec 128) : BitVec 128 :=
  VG.Proof.Gcm.X86.Pclmul.catWord (VG.Proof.Gcm.X86.Pclmul.catWord (VG.Proof.Gcm.X86.Pclmul.catWord ((0 : BitVec 96) ++ c.extractLsb' 96 32)
    (c.extractLsb' 64 32)) (c.extractLsb' 32 32)) (c.extractLsb' 0 32)

theorem assembled_eq (c : BitVec 128) : VG.Proof.Gcm.X86.Pclmul.assembled c = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [VG.Proof.Gcm.X86.Pclmul.assembled, VG.Proof.Gcm.X86.Pclmul.catWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i)
    with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true,
      decide_eq_false, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_or, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.or_false] <;>
    exact congrArg _ (by omega)

/-- Setup changes only eax and the listed vector registers. -/
structure SetupFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem const_ok (r : XReg) (c : BitVec 128) (s : State) (hr : r ≠ .xmm5) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.const r c)) s fun s' =>
      s'.xmm r = c ∧ VG.Proof.Gcm.X86.Pclmul.SetupFrame [r, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.const, List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append]
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    hr, Option.map_some, Option.some.injEq,
    exists_eq_left', XShiftOp.eval, XBinOp.eval]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · exact VG.Proof.Gcm.X86.Pclmul.assembled_eq c
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
  · simp only [mem_setXmm, mem_setReg]
  · simp only [rd_setXmm, rd_setReg]
  · simp only [wr_setXmm, wr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2, ite_false]

theorem unpack_ones : XBinOp.eval .punpckldq
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32))
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32)) =
    ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) := rfl

theorem hInv_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.hInv) s fun s' =>
      VG.Proof.Gcm.Poly.x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      VG.Proof.Gcm.X86.Pclmul.SetupFrame [.xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  rw [Impl.Gcm.X86.Pclmul.hInv, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.const_ok .xmm4 Impl.Gcm.X86.Pclmul.xInv s (by decide))
    fun s₁ ⟨hc, hf⟩ => ?_
  have h7 : s₁.xmm .xmm7 = s.xmm .xmm7 := hf.xmm _ (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    Option.map_some, Option.some.injEq, exists_eq_left',
    hc, h7, eval_movdqa, VG.Proof.Gcm.X86.Pclmul.eval_pxor, VG.Proof.Gcm.X86.Pclmul.unpack_ones]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · change VG.Proof.Gcm.Poly.x * φ ((XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
      XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) ^^^ _) = _
    rw [VG.Proof.Gcm.X86.Pclmul.shl1, VG.Proof.Gcm.X86.Pclmul.mask_eq, VG.Proof.Gcm.X86.Pclmul.x_φ_hInv]
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
    exact hf.gpr a ha
  · simp only [mem_setXmm, mem_setReg]; exact hf.mem
  · simp only [rd_setXmm, rd_setReg]; exact hf.rd
  · simp only [wr_setXmm, wr_setReg]; exact hf.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2.2.1, ha.2.2.2, ite_false]
    exact hf.xmm a (by simp only [List.mem_cons, List.not_mem_nil,
      ha.2.1, ha.2.2.1, or_self, not_false_eq_true])

end VG.Proof.Gcm.X86.Pclmul

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Invariant`.
section

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd
open VG.Impl.Gcm.X86.Pclmul (at_ argOp)
open VG.Proof.Gcm.X86 (GPre aR)

theorem args_in {s : State} (hp : GPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  refine ⟨aR s, by simp only [hp.rd, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_true, true_or], ?_⟩
  exact Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20)
    hp.fSp (by decide) (by omega) (by omega) (by decide)

theorem ea_arg (s : State) (i : Nat) : s.ea (VG.Impl.Gcm.X86.Pclmul.argOp i) = argAddr s i := rfl

theorem movArg_exec {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : i < 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (d : Reg) :
    exec (.mov d (.mem (VG.Impl.Gcm.X86.Pclmul.argOp i))) s = some (s.setReg d (VG.X86.arg s₀ i)) := by
  have he : s.ea (VG.Impl.Gcm.X86.Pclmul.argOp i) = argAddr s₀ i := by
    simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.argOp, VG.Impl.Gcm.X86.Pclmul.at_, argAddr, hsp]
  simp only [exec, readSrc, State.load32, he, hrd, hwr, VG.Proof.Gcm.X86.Pclmul.args_in hp hi,
    ite_true, hm, Option.map_some, VG.X86.arg]

/-- Load a big-endian GHASH block, retaining every general-purpose register. -/
theorem ldrev_ok (r : XReg) (b : Reg) (d : Nat) (s : State) (hr : r ≠ .xmm0)
    (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Gcm.X86.Pclmul.at_ b d)) 16) :
    WP isa (.block [.movdquLoad r (VG.Impl.Gcm.X86.Pclmul.at_ b d), .xop (.bin .pshufb r .xmm0)]) s fun s' =>
      s'.xmm r = Spec.Gcm.blockAt s.mem (s.ea (VG.Impl.Gcm.X86.Pclmul.at_ b d)) ∧ VG.Proof.Gcm.X86.Pclmul.Only [r] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, XOp.exec, State.load128, hin, xmm_setXmm, Ne.symm hr,
    h0, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun a ha => ?_⟩
  · rw [VG.Proof.Gcm.X86.blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [xmm_setXmm, ha, ite_false]

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- Every instruction before the final Y store retains memory, regions and
all cdecl callee-saved registers. -/
structure Env (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem Env.refl (s : State) : VG.Proof.Gcm.X86.Pclmul.Env s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Env.sp {s₀ s : State} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Env.of_setup {s₀ s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s)
    (hf : VG.Proof.Gcm.X86.Pclmul.SetupFrame rs s s') : VG.Proof.Gcm.X86.Pclmul.Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr, fun r hr => by
    have hn : r ≠ .eax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hf.gpr r hn).trans (h.saved r hr)⟩

theorem Env.of_only {s₀ s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s)
    (hf : VG.Proof.Gcm.X86.Pclmul.Only rs s s') : VG.Proof.Gcm.X86.Pclmul.Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (congrFun hf.gpr r).trans (h.saved r hr)⟩

theorem Env.setReg {s₀ s : State} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s) (d : Reg) (v : BitVec 32)
    (hd : d ∉ calleeSaved) : VG.Proof.Gcm.X86.Pclmul.Env s₀ (s.setReg d v) :=
  ⟨(mem_setReg s d v).trans h.mem, (rd_setReg s d v).trans h.rd,
    (wr_setReg s d v).trans h.wr, fun r hr => by
    rw [gpr_setReg_of_ne s v (show r ≠ d from fun heq => hd (heq ▸ hr))]
    exact h.saved r hr⟩

abbrev H (s₀ : State) : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem ((hP s₀).setWidth 64)
abbrev Y (s₀ : State) (i : Nat) : VG.Spec.Gcm.Block :=
  ghashFrom (VG.Proof.Gcm.X86.Pclmul.H s₀) (VG.Spec.Gcm.blockAt s₀.mem ((yP s₀).setWidth 64))
    (VG.Spec.Gcm.blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- The accumulator after i blocks and public remaining count/data pointer. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  env : VG.Proof.Gcm.X86.Pclmul.Env s₀ s
  le : i ≤ VG.Proof.Gcm.X86.nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.Gcm.X86.nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  out : s.gpr .ecx = yP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  hash : VG.Proof.Gcm.Poly.x * φ (s.xmm .xmm3) = φ (VG.Proof.Gcm.X86.Pclmul.H s₀)
  acc : s.xmm .xmm2 = VG.Proof.Gcm.X86.Pclmul.Y s₀ i

end VG.Proof.Gcm.X86.Pclmul

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Body`.
section

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk hR yR)
open VG.Impl.Gcm.X86.Pclmul (argOp at_)

theorem Env.arithFlags {s₀ s : State} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s) (v : BitVec 32) (c o : Bool) :
    VG.Proof.Gcm.X86.Pclmul.Env s₀ (VG.X86.arithFlags s v c o) :=
  ⟨(mem_arithFlags s v c o).trans h.mem, (rd_arithFlags s v c o).trans h.rd,
    (wr_arithFlags s v c o).trans h.wr,
    fun r hr => by rw [gpr_arithFlags]; exact h.saved r hr⟩

theorem movArg_ok {s₀ s : State} (hp : GPre s₀) (he : VG.Proof.Gcm.X86.Pclmul.Env s₀ s)
    (i : Nat) (hi : i < 5) (d : Reg) (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (VG.Impl.Gcm.X86.Pclmul.argOp i))]) s fun s' =>
      s'.gpr d = VG.X86.arg s₀ i ∧ VG.Proof.Gcm.X86.Pclmul.Env s₀ s' ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨s.setReg d (VG.X86.arg s₀ i), ?_, ?_⟩
  · rw [runBlock_cons, VG.Proof.Gcm.X86.Pclmul.movArg_exec hp hi he.sp he.mem he.rd he.wr,
      runStep_some, runBlock_nil]
  · exact ⟨gpr_setReg_self _ _ _, he.setReg d _ hd,
      fun r hr => gpr_setReg_of_ne _ _ hr, rfl⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun s' =>
      s'.zf = some (s.gpr .eax == 0) ∧ VG.Proof.Gcm.X86.Pclmul.Env s s' ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨VG.X86.arithFlags s (s.gpr .eax) false false, ?_, ?_⟩
  · simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some,
      BitVec.and_self, runStep_some, runBlock_nil]
  · exact ⟨rfl, (Env.refl s).arithFlags _ _ _, rfl, rfl⟩

theorem h_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((hP s).setWidth 64) 16 := by
  refine ⟨VG.Proof.Gcm.X86.hR s, ?_, Region.contains_self _ _⟩
  simp only [hp.rd, List.mem_append, List.mem_cons, true_or]

theorem y_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((yP s).setWidth 64) 16 := by
  refine ⟨yR s, ?_, Region.contains_self _ _⟩
  simp only [hp.wr, List.mem_append, List.mem_cons, or_true, true_or]

theorem Env.trans {s₀ s s' : State} (h : VG.Proof.Gcm.X86.Pclmul.Env s₀ s) (h' : VG.Proof.Gcm.X86.Pclmul.Env s s') : VG.Proof.Gcm.X86.Pclmul.Env s₀ s' :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.saved r hr).trans (h.saved r hr)⟩

theorem prologue_ok (s₀ : State) (hp : GPre s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.prologue) s₀ fun s =>
      VG.Proof.Gcm.X86.Pclmul.Inv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.Gcm.X86.nBlk s₀ = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.const_ok .xmm0 Impl.Gcm.X86.Pclmul.revMask s₀ (by decide))
    fun s₁ ⟨rev₁, f₁⟩ => ?_
  have e₁ := (Env.refl s₀).of_setup f₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.const_ok .xmm1 Impl.Gcm.X86.Pclmul.poly s₁ (by decide))
    fun s₂ ⟨poly₂, f₂⟩ => ?_
  have e₂ := e₁.of_setup f₂
  have rev₂ : s₂.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₂.xmm _ (by decide), rev₁]; rfl
  rw [show ([.mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 0)), .movdquLoad .xmm7 (VG.Impl.Gcm.X86.Pclmul.at_ .eax 0),
      .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) =
      ([.mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 0))] : List Instr) ++
      [.movdquLoad .xmm7 (VG.Impl.Gcm.X86.Pclmul.at_ .eax 0), .xop (.bin .pshufb .xmm7 .xmm0)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.movArg_ok hp e₂ 0 (by decide) .eax (by decide))
    fun s₃ ⟨ptr₃, e₃, _, x₃⟩ => ?_
  have hread₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.ea (VG.Impl.Gcm.X86.Pclmul.at_ .eax 0)) 16 := by
    simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, ptr₃, BitVec.add_zero, e₃.rd, e₃.wr]
    exact VG.Proof.Gcm.X86.Pclmul.h_read hp
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.ldrev_ok .xmm7 .eax 0 s₃ (by decide) (by rw [x₃]; exact rev₂) hread₃)
    fun s₄ ⟨hash₄, f₄⟩ => ?_
  have e₄ := e₃.of_only f₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.hInv_ok s₄) fun s₅ ⟨hash₅, f₅⟩ => ?_
  have e₅ := e₄.of_setup f₅
  have rev₅ : s₅.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact rev₂
  have poly₅ : s₅.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact poly₂
  have hash₅' : VG.Proof.Gcm.Poly.x * φ (s₅.xmm .xmm3) = φ (VG.Proof.Gcm.X86.Pclmul.H s₀) := by
    rw [hash₅, hash₄, e₃.mem]
    simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, ptr₃, BitVec.add_zero]
  change WP isa (.block (([.mov .ecx (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 1))] : List Instr) ++
    [.movdquLoad .xmm2 (VG.Impl.Gcm.X86.Pclmul.at_ .ecx 0), .xop (.bin .pshufb .xmm2 .xmm0),
      .mov .edx (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 2)), .mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 3)), .alu .test .eax (.reg .eax)])) s₅ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.movArg_ok hp e₅ 1 (by decide) .ecx (by decide))
    fun s₆ ⟨ptr₆, e₆, _, x₆⟩ => ?_
  have yread₆ : InRegions (s₆.rd ++ s₆.wr) (s₆.ea (VG.Impl.Gcm.X86.Pclmul.at_ .ecx 0)) 16 := by
    simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, ptr₆, BitVec.add_zero, e₆.rd, e₆.wr]
    exact VG.Proof.Gcm.X86.Pclmul.y_read hp
  change WP isa (.block (([.movdquLoad .xmm2 (VG.Impl.Gcm.X86.Pclmul.at_ .ecx 0),
    .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++
    [.mov .edx (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 2)), .mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 3)), .alu .test .eax (.reg .eax)])) s₆ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.ldrev_ok .xmm2 .ecx 0 s₆ (by decide) (by rw [x₆]; exact rev₅) yread₆)
    fun s₇ ⟨acc₇, f₇⟩ => ?_
  have e₇ := e₆.of_only f₇
  change WP isa (.block (([.mov .edx (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 2))] : List Instr) ++
    [.mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 3)), .alu .test .eax (.reg .eax)])) s₇ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.movArg_ok hp e₇ 2 (by decide) .edx (by decide))
    fun s₈ ⟨ptr₈, e₈, regs₈, x₈⟩ => ?_
  change WP isa (.block (([.mov .eax (.mem (VG.Impl.Gcm.X86.Pclmul.argOp 3))] : List Instr) ++
    [.alu .test .eax (.reg .eax)])) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.movArg_ok hp e₈ 3 (by decide) .eax (by decide))
    fun s₉ ⟨count₉, e₉, regs₉, x₉⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.test_ok s₉) fun s ⟨zf, ef, regs, xs⟩ => ?_
  constructor
  · refine ⟨e₉.trans ef, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regs, count₉, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [regs, regs₉ _ (by decide), ptr₈, Nat.mul_zero, BitVec.add_zero]
    · rw [regs, regs₉ _ (by decide), regs₈ _ (by decide), f₇.gpr, ptr₆]
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact rev₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact poly₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact hash₅'
    · rw [xs, x₉, x₈, acc₇, e₆.mem]
      simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, ptr₆, BitVec.add_zero,
        VG.Proof.Gcm.X86.Pclmul.Y, Proof.Gcm.ghashFrom_blocksAt_zero]
  · rw [zf, count₉]
    exact congrArg some (by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Wp.ofNat_beq_zero (VG.X86.arg s₀ 3).isLt)

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre dP nBlk dR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem data_read {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : VG.Proof.Gcm.X86.Pclmul.Inv s₀ i s)
    (hb : i < VG.Proof.Gcm.X86.nBlk s₀) :
    InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Gcm.X86.Pclmul.at_ .edx 0)) 16 := by
  have hf := hp.fD
  have he : s.ea (VG.Impl.Gcm.X86.Pclmul.at_ .edx 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega)
  rw [he, hi.env.rd, hi.env.wr, hp.rd]
  refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

theorem xor_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm2 .xmm7)]) s fun s' =>
      s'.xmm .xmm2 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ VG.Proof.Gcm.X86.Pclmul.Only [.xmm2] s s' := by
  refine WP.of_runBlock ⟨s.setXmm .xmm2 (s.xmm .xmm2 ^^^ s.xmm .xmm7), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, XBinOp.eval, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro r hr
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]) s fun s' =>
      s'.gpr .eax = s.gpr .eax - 1 ∧ s'.gpr .edx = s.gpr .edx + 16 ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧ VG.Proof.Gcm.X86.Pclmul.Env s s' ∧
      s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact (((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _ |>.setReg .eax _ (by decide)

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : VG.Proof.Gcm.X86.Pclmul.Inv s₀ i s)
    (hb : i < VG.Proof.Gcm.X86.nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body) s fun s' =>
      VG.Proof.Gcm.X86.Pclmul.Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (VG.Proof.Gcm.X86.nBlk s₀ - (i + 1) = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.body, List.append_assoc]
  rw [show ([.movdquLoad .xmm7 (VG.Impl.Gcm.X86.Pclmul.at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) =
    ([.movdquLoad .xmm7 (VG.Impl.Gcm.X86.Pclmul.at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++
    [.xop (.bin .pxor .xmm2 .xmm7)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.ldrev_ok .xmm7 .edx 0 s (by decide) hi.rev (VG.Proof.Gcm.X86.Pclmul.data_read hp hi hb))
    fun s₁ ⟨input₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.xor_ok s₁) fun s₂ ⟨acc₂, f₂⟩ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have env₃ := ((hi.env.of_only f₁).of_only f₂).of_only f₃
  have acc₃ : s₃.xmm .xmm2 = VG.Proof.Gcm.X86.Pclmul.Y s₀ (i + 1) := by
    apply φ_inj
    have hin : s₁.xmm .xmm7 = Spec.Gcm.blockAt s₀.mem
        ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) := by
      rw [input₁, hi.env.mem]
      refine congrArg (Spec.Gcm.blockAt _) ?_
      simp only [State.ea, VG.Impl.Gcm.X86.Pclmul.at_, hi.data, BitVec.add_zero]
      exact addr_eq (by have hf := hp.fD; omega)
    rw [mul₃, acc₂, hin, f₁.xmm _ (by decide), hi.acc]
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]
    rw [mul_assoc, mul_left_comm VG.Proof.Gcm.Poly.x, hi.hash]
    rw [show VG.Proof.Gcm.X86.Pclmul.Y s₀ (i + 1) = Spec.Gcm.mul (VG.Proof.Gcm.X86.Pclmul.Y s₀ i ^^^ Spec.Gcm.blockAt s₀.mem
      ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i))) (VG.Proof.Gcm.X86.Pclmul.H s₀) from
      Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul]
  refine WP.mono (VG.Proof.Gcm.X86.Pclmul.advance_ok s₃) fun s₄ ⟨count₄, data₄, zf₄, ef₄, out₄, xmm₄⟩ => ?_
  have regs₃ : s₃.gpr = s.gpr := f₃.gpr.trans (f₂.gpr.trans f₁.gpr)
  have bound : VG.Proof.Gcm.X86.nBlk s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  have count : s₃.gpr .eax - 1 = BitVec.ofNat 32 (VG.Proof.Gcm.X86.nBlk s₀ - (i + 1)) := by
    rw [regs₃, hi.count, Wp.ofNat_pred (by omega), Nat.sub_sub]
  constructor
  · refine ⟨env₃.trans ef₄, by omega, count₄.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [data₄, regs₃, hi.data, BitVec.add_assoc]
      change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
      rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
    · rw [out₄, regs₃]; exact hi.out
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
    · rw [xmm₄, f₃.xmm _ (by decide)]; exact poly₂
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.hash
    · rw [xmm₄]; exact acc₃
  · rw [zf₄, count, Wp.ofNat_beq_zero (by omega)]

end VG.Proof.Gcm.X86.Pclmul

end

section

section

namespace VG.Impl.Gcm.X86.Pclmul
materialize_code ghash
end VG.Impl.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86.pre
    Proof.Gcm.ghashX86.pub Impl.Gcm.X86.Pclmul.ghash :=
  VG.Taint.constantTime (A := sseTaint) Proof.Gcm.X86.ghτ₀
    (fun _ _ h₁ h₂ hp => Proof.Gcm.X86.gh_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Gcm.X86 (GPre yP nBlk yR rR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem blocks_ok {s₀ s : State} (hp : GPre s₀) (hi : VG.Proof.Gcm.X86.Pclmul.Inv s₀ 0 s) (hn : 0 < VG.Proof.Gcm.X86.nBlk s₀) :
    WP isa (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne) s (VG.Proof.Gcm.X86.Pclmul.Inv s₀ (VG.Proof.Gcm.X86.nBlk s₀)) := by
  refine WP.loop (M := isa) (fun k s => ∃ i,
    k = VG.Proof.Gcm.X86.nBlk s₀ - i ∧ i < VG.Proof.Gcm.X86.nBlk s₀ ∧ VG.Proof.Gcm.X86.Pclmul.Inv s₀ i s)
    (fun k s ⟨i, hk, hb, hs⟩ => WP.mono (VG.Proof.Gcm.X86.Pclmul.body_ok hp hs hb) fun s' ⟨inv, z⟩ => ?_)
    (VG.Proof.Gcm.X86.nBlk s₀) s ⟨0, rfl, hn, hi⟩
  by_cases hl : i + 1 = VG.Proof.Gcm.X86.nBlk s₀
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at inv; exact inv
  · exact .inr ⟨by simp [X86.eval, z]; omega,
      VG.Proof.Gcm.X86.nBlk s₀ - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem epilogue_ok {s₀ s : State} (hp : GPre s₀) (hi : VG.Proof.Gcm.X86.Pclmul.Inv s₀ (VG.Proof.Gcm.X86.nBlk s₀) s) :
    WP isa (.block Impl.Gcm.X86.Pclmul.epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  have writable : InRegions s.wr ((yP s₀).setWidth 64) 16 := by
    rw [hi.env.wr, hp.wr]
    exact ⟨yR s₀, by simp, Region.contains_self _ _⟩
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.epilogue, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.store128, gpr_setXmm, wr_setXmm, State.ea, VG.Impl.Gcm.X86.Pclmul.at_, hi.out, BitVec.add_zero, writable,
    ite_true, mem_setXmm, xmm_setXmm_self, hi.rev,
    Option.some.injEq, exists_eq_left']
  constructor
  · constructor
    · intro r hr
      exact hi.env.saved r hr
    · rw [hi.env.mem, Mem.readW_writeW_sep
        (hp.rY.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
  · change Spec.Gcm.blockAt (s.mem.writeW ((yP s₀).setWidth 64)
      (XBinOp.eval .pshufb (s.xmm .xmm2) VG.Proof.Gcm.X86.revMask)) ((yP s₀).setWidth 64) = _
    rw [Proof.Gcm.X86.blockAt_store, hi.acc]

theorem gh_correct (s₀ : State) (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.Pclmul.ghash s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  unfold Impl.Gcm.X86.Pclmul.ghash
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86.Pclmul.prologue_ok s₀ hp) fun s₁ ⟨hi, z⟩ => ?_)
  have loop : WP isa (.ite .e (.block []) (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne))
      s₁ (VG.Proof.Gcm.X86.Pclmul.Inv s₀ (VG.Proof.Gcm.X86.nBlk s₀)) := by
    refine WP.ite (decide (VG.Proof.Gcm.X86.nBlk s₀ = 0)) (by simp only [X86.eval, z]) ?_ ?_
    · intro h
      have hn : VG.Proof.Gcm.X86.nBlk s₀ = 0 := of_decide_eq_true h
      rw [hn]; exact WP.block_nil hi
    · intro h
      have hn : 0 < VG.Proof.Gcm.X86.nBlk s₀ := by
        have hne : VG.Proof.Gcm.X86.nBlk s₀ ≠ 0 := of_decide_eq_false h
        omega
      exact VG.Proof.Gcm.X86.Pclmul.blocks_ok hp hi hn
  exact WP.seq (WP.mono loop fun s₂ inv => VG.Proof.Gcm.X86.Pclmul.epilogue_ok hp inv)

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.Pclmul.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashX86.post s s' := VG.Proof.Gcm.X86.Pclmul.gh_correct s (GPre.of hs)

theorem ghash_verified :
    Verified X86.target Impl.Gcm.X86.Pclmul.ghash (Spec.Gcm.ghashContract X86.abi) :=
  Verified.of_correct VG.Proof.Gcm.X86.Pclmul.ghash_correct VG.Proof.Gcm.X86.Pclmul.ghash_ct
    (by
      open VG.Proof.Gcm.X86 in
      have a0 : VG.X86.arg ghSat 0 = 0x1000 := by decide
      have a1 : VG.X86.arg VG.Proof.Gcm.X86.ghSat 1 = 0x2000 := by decide
      have a2 : VG.X86.arg VG.Proof.Gcm.X86.ghSat 2 = 0x3000 := by decide
      have a3 : VG.X86.arg VG.Proof.Gcm.X86.ghSat 3 = 0 := by decide
      have a4 : VG.X86.arg VG.Proof.Gcm.X86.ghSat 4 = 0x4000 := by decide
      have e : argAddr VG.Proof.Gcm.X86.ghSat 0 = 0x8004 := by decide
      have esp : VG.Proof.Gcm.X86.ghSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Gcm.ghashX86]
        [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Gcm.X86.ghSat)

end VG.Proof.Gcm.X86.Pclmul

end
