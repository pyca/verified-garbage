module

public import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.X86.Rev
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Gcm.X86.Ghash
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Impl.Gcm.X86.Pclmul
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Impl.Gcm.X86.Pclmul
meta import VerifiedGarbage.Proof.Framework.InstancePriority
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Gcm.X86.Pclmul.Arith`, which only this module used -/

section

@[expose] public section

section

section

/-!
# GHASH with PCLMULQDQ: the arithmetic

Untrusted: everything here is checked by Lean. What the instructions of
`Impl.Gcm.X86.Pclmul` compute, in the ring `Q` of `Proof/Gcm/Poly.lean`:

* `pclmulqdq` multiplies polynomials (`gp_clmul`), so the four of `mul4`
  compute `x · a · b` as a 256-bit value (`Prod.val_mul`), and the three of
  `kblock` add it to one, whose middle part is then the sum of the three
  (`Prod.val_kacc`);
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
  · simp only [h, ite_true, decide_eq_true (show 128 - 64 ≤ d + j by omega_using [h]), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega_using [hj]))
  · simp only [h, ite_false, decide_eq_false (show ¬ 128 - 64 ≤ d + j by omega_using [h]), Bool.false_and]; rfl

/-- The first `k` steps of `clmul`. -/
def clSteps (a b : BitVec 64) (k : Nat) : BitVec 128 :=
  (List.range k).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

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
    · rw [gp_xor, ih (by omega_using [hk]), gp_shl b (by omega_using [hk]),
        show 64 - k = 63 - k + 1 by omega_using [hk], pow_succ]
      ring
    · rw [ih (by omega_using [hk])]; ring

theorem gp_lsb (a : BitVec 64) :
    (∑ i ∈ Finset.range 64, if a.getLsbD i then (X : P) ^ (63 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega_using [hi]), Bool.true_and,
    show 64 - 1 - i = 63 - i by omega_using [], show 63 - (64 - 1 - i) = i by omega_using [hi]]

/-- `pclmulqdq` multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_clmul (a b : BitVec 64) : gp (clmul a b) = X * gp a * gp b := by
  rw [show clmul a b = clSteps a b 64 from rfl, gp_clSteps a b (Nat.le_refl _), gp_lsb]

/-! ## Quadwords -/

theorem qwords (v : BitVec 128) : v = qword v 1 ++ qword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, mul_zero, zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega_using [hi]), Bool.true_and]
    exact congrArg _ (by omega_using [h])

theorem gp_qwords (v : BitVec 128) : gp v = gp (qword v 1) + X ^ 64 * gp (qword v 0) := by
  conv => lhs; rw [qwords v]
  rw [gp_append]

theorem φ_qwords (v : BitVec 128) :
    φ v = AdjoinRoot.mk g (gp (qword v 1)) + x ^ 64 * AdjoinRoot.mk g (gp (qword v 0)) := by
  rw [φ, gp_qwords]; simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X]

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem φ_clmul (a b : BitVec 64) : φ (clmul a b) = x * ψ a * ψ b := by
  simp only [φ, ψ, gp_clmul, map_mul, AdjoinRoot.mk_X]

theorem φ_q (v : BitVec 128) : φ v = ψ (qword v 1) + x ^ 64 * ψ (qword v 0) := φ_qwords v

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

/-- The four products of `mul4`. -/
def mul (a b : BitVec 128) : Prod :=
  ⟨pclmul a b 0x00, pclmul a b 0x01 ^^^ pclmul a b 0x10, pclmul a b 0x11⟩

def zero : Prod := ⟨0, 0, 0⟩

theorem val_mul (a b : BitVec 128) : (mul a b).val = x * φ a * φ b := by
  simp only [mul, val, φ_xor]
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x01 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x01 : BitVec 8).getLsbD 4 = false from rfl, show (0x10 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x10 : BitVec 8).getLsbD 4 = true from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    φ_clmul, φ_q a, φ_q b]
  ring

end Prod

/-! ## Three multiplications for a product -/

/-- The sum of the halves of a block. -/
def halfSum (v : BitVec 128) : BitVec 64 := qword v 1 ^^^ qword v 0

theorem ψ_xor (a b : BitVec 64) : ψ (a ^^^ b) = ψ a + ψ b := by
  simp only [ψ, gp_xor, map_add]

namespace Prod

/-- The three products of `kblock`, added to `p`: of the low halves, of the
sums of the halves, and of the high halves. -/
def kacc (p : Prod) (a b : BitVec 128) : Prod :=
  ⟨p.lo ^^^ pclmul a b 0x00, p.mid ^^^ clmul (halfSum a) (halfSum b), p.hi ^^^ pclmul a b 0x11⟩

/-- The product whose middle part is the sum of the three of `p`
(`kmiddle`). -/
def kfix (p : Prod) : Prod := ⟨p.lo, p.mid ^^^ p.lo ^^^ p.hi, p.hi⟩

theorem kfix_zero : zero.kfix.val = 0 := by
  simp only [kfix, val, zero, BitVec.ofNat_eq_ofNat, BitVec.xor_self, φ_zero', mul_zero, add_zero]

theorem val_kacc (p : Prod) (a b : BitVec 128) :
    (p.kacc a b).kfix.val = p.kfix.val + x * φ a * φ b := by
  simp only [kacc, kfix, val, φ_xor]
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    φ_clmul, halfSum, ψ_xor, φ_q a, φ_q b]
  linear_combination
    (x ^ 65 * (ψ (qword a 0) * ψ (qword b 0) + ψ (qword a 1) * ψ (qword b 1))) * two_Q

end Prod

/-! ## The reduction -/

theorem shr64 (v : BitVec 128) : v >>> 64 = 0#64 ++ qword v 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · simp only [h, ite_false, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge _ _ (by omega_using [h])

theorem shl64 (v : BitVec 128) : v <<< 64 = qword v 0 ++ 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  by_cases h : i < 64
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, ↓reduceIte, BitVec.getLsbD_eq_getElem, BitVec.getElem_zero]
  · simp only [h, ite_false, decide_false, Bool.not_false, Bool.true_and, Nat.mul_zero, Nat.zero_add,
      decide_eq_true (show i - 64 < 64 by omega_using [hi]), decide_eq_true hi, Bool.and_true]

theorem φ_shr64 (v : BitVec 128) : φ (v >>> 64) = x ^ 64 * ψ (qword v 1) := by
  rw [φ, shr64, gp_append, gp_zero']; simp only [zero_add, map_mul, map_pow, AdjoinRoot.mk_X, ψ]

theorem φ_shl64 (v : BitVec 128) : φ (v <<< 64) = ψ (qword v 0) := by
  rw [φ, shl64, gp_append, gp_zero']; simp only [mul_zero, add_zero, ψ]

theorem ψ_c : ψ (qword poly 1) = 1 + x + x ^ 6 := by
  have hb : ∀ d < 64, (qword poly 1).getMsbD d = (d = 0 || d = 1 || d = 6) := by decide +kernel
  have h : gp (qword poly 1) = 1 + X + X ^ 6 := by
    ext d
    rw [coeff_gp]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    by_cases hd : d < 64
    · rw [hb d hd]
      rcases (by omega_using [] : d = 0 ∨ d = 1 ∨ d = 6 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6)) with
        rfl | rfl | rfl | ⟨h0, h1, h6⟩
      · decide
      · decide
      · decide
      · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : (qword poly 1).getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega_using [hd]
      rw [e]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega_using [hd], show (1 : Nat) ≠ d by omega_using [hd], add_zero, show d ≠ 6 by omega_using [hd]]
  simp only [ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem shufDwords_4e (a : BitVec 128) : shufDwords a 0x4e = qword a 0 ++ qword a 1 := by
  rw [show shufDwords a 0x4e = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_ofDwords, getLsbD_dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega_using [] : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega_arith)

theorem qword_append_0 (h l : BitVec 64) : qword (h ++ l) 0 = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_zero, Nat.zero_add, ite_true]

theorem qword_append_1 (h l : BitVec 64) : qword (h ++ l) 1 = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_one, show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]

/-- The low quadword of a block added to itself with its halves swapped is
the sum of its halves. -/
theorem qword_swapXor (a : BitVec 128) : qword (shufDwords a 0x4e ^^^ a) 0 = halfSum a := by
  rw [shufDwords_4e]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [halfSum, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add, Nat.mul_one, ite_true]

/-- `kblock`'s third multiplication: the low quadword of its first operand
by the quadword `k % 2` of the second. -/
theorem pclmul_halfSel (a b : BitVec 128) (k : Nat) :
    pclmul a b (Impl.Gcm.X86.Pclmul.halfSel k) = clmul (qword a 0) (qword b (k % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [Impl.Gcm.X86.Pclmul.halfSel, h] <;> rfl

/-- One step of the reduction: `swap(v) ⊕ clmul(v₀, c)`. -/
def fold (v : BitVec 128) : BitVec 128 := shufDwords v 0x4e ^^^ pclmul v poly 0x10

theorem φ_fold (v : BitVec 128) : φ (fold v) = x ^ 64 * φ v := by
  have e1 : φ (shufDwords v 0x4e) = ψ (qword v 0) + x ^ 64 * ψ (qword v 1) := by
    rw [shufDwords_4e, φ, gp_append]; simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, ψ]
  have e2 : pclmul v poly 0x10 = clmul (qword v 0) (qword poly 1) := rfl
  rw [fold, φ_xor, e1, e2, φ_clmul, ψ_c, φ_q v]
  linear_combination (-ψ (qword v 0)) * x128

/-- The block `reduce` computes from a product. -/
def reduce (p : Prod) : BitVec 128 :=
  (p.hi ^^^ p.mid >>> 64) ^^^ fold (fold (p.lo ^^^ p.mid <<< 64))

theorem φ_reduce (p : Prod) : φ (reduce p) = p.val := by
  simp only [reduce, φ_xor, φ_fold, φ_shr64, φ_shl64, Prod.val, φ_q p.mid]
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
  rcases (by omega_using [] : i = 0 ∨ (1 ≤ i ∧ i < 64) ∨ i = 64 ∨ 64 < i) with h | h | h | h
  · subst h; simp only [Nat.ofNat_pos, ↓reduceIte, decide_true, Order.lt_one_iff, Bool.not_true, Bool.and_false, zero_tsub, mul_zero, add_zero, BitVec.getLsbD_eq_getElem, Bool.true_and, Bool.false_and, Nat.lt_add_one, zero_add, Nat.reduceLT, Bool.or_self]
  · simp (disch := omega) only [ite_eq_left, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true, Bool.not_true]
    exact congrArg _ (by omega_using [])
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true,
      Bool.not_true]
    exact congrArg _ (by omega_using [h])

theorem shr31 (y : BitVec 32) : y >>> 31 = if y.msb then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  have := y.isLt
  split_ifs with h
  · simp only [Nat.add_one_sub_one, Nat.reducePow, decide_eq_true_eq] at h; simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat, Nat.one_mod]; omega_using [h]
  · simp only [Nat.add_one_sub_one, Nat.reducePow, decide_eq_true_eq, not_le] at h; simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat, Nat.zero_mod, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, gt_iff_lt]; omega_using [h]

theorem msb_dword3 (h : BitVec 128) : dword h 3 >>> 31 = if h.getMsbD 0 then 1#32 else 0#32 := by
  have e : (dword h 3).msb = h.getMsbD 0 := by
    simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword, BitVec.getMsbD]; rfl
  rw [shr31, e]

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
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, msb_dword3]
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
    rcases (by omega_using [] : d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 127 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h6, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, h7, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv.getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega_using [hd]
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega_using [hd], show (1 : Nat) ≠ d by omega_using [hd], add_zero, show d ≠ 6 by omega_using [hd], show d ≠ 127 by omega_using [hd]]

theorem x_φ_xInv : x * φ xInv = 1 := by
  simp only [φ, gp_xInv, map_add, map_one, map_pow, AdjoinRoot.mk_X]
  linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q

theorem gp_shl1 (h : BitVec 128) : X * gp (h <<< 1) + C (bit (h.getMsbD 0)) = gp h := by
  ext d
  rw [coeff_add, coeff_C, coeff_gp]
  rcases d with _ | d
  · simp only [mul_coeff_zero, coeff_X_zero, zero_mul, ↓reduceIte, zero_add]
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]; simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]

/-- `hInv`'s result is `H · x⁻¹`. -/
theorem x_φ_hInv (h : BitVec 128) :
    x * φ ((h <<< 1) ^^^ (if h.getMsbD 0 then xInv else 0)) = φ h := by
  have e := congrArg (AdjoinRoot.mk g) (gp_shl1 h)
  simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at e
  rw [φ_xor, mul_add]
  change x * AdjoinRoot.mk g (gp (h <<< 1)) + _ = AdjoinRoot.mk g (gp h)
  rw [← e]
  split_ifs with hb
  · rw [x_φ_xInv, hb]; simp only [bit, ↓reduceIte, map_one]
  · rw [φ_zero, Bool.not_eq_true] at *; rw [hb]; simp only [mul_zero, add_zero, bit, Bool.false_eq_true, ↓reduceIte, map_zero]

end VG.Proof.Gcm.X86.Pclmul

end


end

end

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Const`.

@[expose] public section

section

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86.Pclmul (at_ poly xInv)

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := rfl

theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< 64 := rfl

/-- `s'` differs from `s` at most in the SSE registers `rs`. -/
structure Only (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem Only.trans {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Only.weaken {rs rs' : List XReg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Only rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.xmm .xmm4, s.xmm .xmm5, s.xmm .xmm6⟩

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.zero) s fun s' =>
      prod s' = Prod.zero ∧ Only [.xmm4, .xmm5, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.zero]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, xmm_setXmm, eval_pxor, BitVec.xor_self, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2, ite_false]

theorem mul4_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.mul4) s fun s' =>
      prod s' = Prod.mul (s.xmm .xmm2) (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm2] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.mul4]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [prod, Prod.mul, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.reduce) s fun s' =>
      s'.xmm .xmm2 = reduce (prod s) ∧ Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.reduce, Impl.Gcm.X86.Pclmul.fold,
    List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    eval_pxor, eval_movdqa, h1, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [prod, psrldq8, pslldq8]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Multiply the accumulator by the transformed hash key. -/
theorem mul_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.mul4 ++ Impl.Gcm.X86.Pclmul.reduce)) s fun s' =>
      φ (s'.xmm .xmm2) = x * φ (s.xmm .xmm2) * φ (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mul4_ok s) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by rw [o₂.xmm _ (by decide), h1]
  refine WP.mono (reduce_ok s₂ e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, φ_reduce, p₂, Prod.val_mul]
  · exact (o₂.trans o₃).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

theorem Only.seq {rs : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs s' s'') :
    Only rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

/-- The registers a block of eight changes. -/
abbrev work : List XReg := [.xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

theorem Only.work {rs : List XReg} {s s' : State} (h : Only rs s s')
    (hs : ∀ r ∈ rs, r ∈ work := by decide) : Only work s s' :=
  h.weaken hs

theorem prod_only {rs : List XReg} {s s' : State} (f : Only rs s s') (h4 : XReg.xmm4 ∉ rs := by decide)
    (h5 : XReg.xmm5 ∉ rs := by decide) (h6 : XReg.xmm6 ∉ rs := by decide) : prod s' = prod s := by
  simp only [prod, f.xmm _ h4, f.xmm _ h5, f.xmm _ h6]

theorem bin_ok (op : XBinOp) (d r : XReg) (s : State) :
    WP isa (.block [.xop (.bin op d r)]) s fun s' =>
      s'.xmm d = op.eval (s.xmm d) (s.xmm r) ∧ Only [d] s s' := by
  refine WP.of_runBlock ⟨s.setXmm d (op.eval (s.xmm d) (s.xmm r)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro a ha
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using ha)

/-- A block's first instruction, on its own. -/
theorem block_one {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: is)) s Q ↔ WP isa (.block [i]) s fun s' => WP isa (.block is) s' Q := by
  show WP isa (.block ([i] ++ is)) s Q ↔ _
  exact WP.block_append_iff

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly

/-- Append a low dword to the lower ninety-six bits of the previous value. -/
def catWord (v : BitVec 128) (d : BitVec 32) : BitVec 128 :=
  (v <<< 32) ||| ((0 : BitVec 96) ++ d)

def assembled (c : BitVec 128) : BitVec 128 :=
  catWord (catWord (catWord ((0 : BitVec 96) ++ c.extractLsb' 96 32)
    (c.extractLsb' 64 32)) (c.extractLsb' 32 32)) (c.extractLsb' 0 32)

theorem assembled_eq (c : BitVec 128) : assembled c = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [assembled, catWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega_using [] : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i)
    with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true,
      decide_eq_false, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_or, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.or_false] <;>
    exact congrArg _ (by omega_arith)

/-- Setup changes only eax and the listed vector registers. -/
structure SetupFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem const_ok (r : XReg) (c : BitVec 128) (s : State) (hr : r ≠ .xmm5) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.const r c)) s fun s' =>
      s'.xmm r = c ∧ SetupFrame [r, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.const, List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append]
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    hr, Option.map_some, Option.some.injEq,
    exists_eq_left', XShiftOp.eval, XBinOp.eval]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · exact assembled_eq c
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
      x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      SetupFrame [.xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  rw [Impl.Gcm.X86.Pclmul.hInv, WP.block_append_iff]
  refine WP.mono (const_ok .xmm4 Impl.Gcm.X86.Pclmul.xInv s (by decide))
    fun s₁ ⟨hc, hf⟩ => ?_
  have h7 : s₁.xmm .xmm7 = s.xmm .xmm7 := hf.xmm _ (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    Option.map_some, Option.some.injEq, exists_eq_left',
    hc, h7, eval_movdqa, eval_pxor, unpack_ones]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · change x * φ ((XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
      XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) ^^^ _) = _
    rw [shl1, mask_eq, x_φ_hInv]
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
    hp.fSp (by decide) (by omega_using []) (by omega_using [hi]) (by decide)

theorem movArg_exec {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : i < 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hsp]
  simp only [exec, readSrc, State.load32, he, hrd, hwr, args_in hp hi,
    ite_true, hm, Option.map_some, arg]

/-- Load a big-endian GHASH block, retaining every general-purpose register. -/
theorem ldrev_ok (r : XReg) (b : Reg) (d : Nat) (s : State) (hr : r ≠ .xmm0)
    (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b d)) 16) :
    WP isa (.block [.movdquLoad r (at_ b d), .xop (.bin .pshufb r .xmm0)]) s fun s' =>
      s'.xmm r = Spec.Gcm.blockAt s.mem (s.ea (at_ b d)) ∧ Only [r] s s' := by
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

theorem Env.refl (s : State) : Env s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Env.sp {s₀ s : State} (h : Env s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Env.of_setup {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : SetupFrame rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr, fun r hr => by
    have hn : r ≠ .eax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hf.gpr r hn).trans (h.saved r hr)⟩

theorem Env.of_only {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : Only rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (congrFun hf.gpr r).trans (h.saved r hr)⟩

theorem Env.setReg {s₀ s : State} (h : Env s₀ s) (d : Reg) (v : BitVec 32)
    (hd : d ∉ calleeSaved) : Env s₀ (s.setReg d v) :=
  ⟨(mem_setReg s d v).trans h.mem, (rd_setReg s d v).trans h.rd,
    (wr_setReg s d v).trans h.wr, fun r hr => by
    rw [gpr_setReg_of_ne s v (show r ≠ d from fun heq => hd (heq ▸ hr))]
    exact h.saved r hr⟩

abbrev H (s₀ : State) : Block := blockAt s₀.mem ((hP s₀).setWidth 64)
abbrev Y (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H s₀) (blockAt s₀.mem ((yP s₀).setWidth 64))
    (blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- The accumulator after i blocks and public remaining count/data pointer. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  env : Env s₀ s
  le : i ≤ nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  out : s.gpr .ecx = yP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  hash : x * φ (s.xmm .xmm3) = φ (H s₀)
  acc : s.xmm .xmm2 = Y s₀ i

end VG.Proof.Gcm.X86.Pclmul

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86.Pclmul.Body`.
section

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk hR yR)
open VG.Impl.Gcm.X86.Pclmul (argOp at_)

theorem Env.arithFlags {s₀ s : State} (h : Env s₀ s) (v : BitVec 32) (c o : Bool) :
    Env s₀ (arithFlags s v c o) :=
  ⟨(mem_arithFlags s v c o).trans h.mem, (rd_arithFlags s v c o).trans h.rd,
    (wr_arithFlags s v c o).trans h.wr,
    fun r hr => by rw [gpr_arithFlags]; exact h.saved r hr⟩

theorem movArg_ok {s₀ s : State} (hp : GPre s₀) (he : Env s₀ s)
    (i : Nat) (hi : i < 5) (d : Reg) (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (argOp i))]) s fun s' =>
      s'.gpr d = arg s₀ i ∧ Env s₀ s' ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨s.setReg d (arg s₀ i), ?_, ?_⟩
  · rw [runBlock_cons, movArg_exec hp hi he.sp he.mem he.rd he.wr,
      runStep_some, runBlock_nil]
  · exact ⟨gpr_setReg_self _ _ _, he.setReg d _ hd,
      fun r hr => gpr_setReg_of_ne _ _ hr, rfl⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun s' =>
      s'.zf = some (s.gpr .eax == 0) ∧ Env s s' ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨arithFlags s (s.gpr .eax) false false, ?_, ?_⟩
  · simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some,
      BitVec.and_self, runStep_some, runBlock_nil]
  · exact ⟨rfl, (Env.refl s).arithFlags _ _ _, rfl, rfl⟩

theorem cmp8_ok (s : State) :
    WP isa (.block [.alu .cmp .eax (.imm 8)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .eax).toNat < 8)) ∧ Env s s' ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨arithFlags s (s.gpr .eax - 8) (decide ((s.gpr .eax).toNat < 8))
    (subOverflow (s.gpr .eax) 8 (s.gpr .eax - 8)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl
  · exact ⟨rfl, (Env.refl s).arithFlags _ _ _, rfl, rfl⟩

theorem h_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((hP s).setWidth 64) 16 := by
  refine ⟨hR s, ?_, Region.contains_self _ _⟩
  simp only [hp.rd, List.mem_append, List.mem_cons, true_or]

theorem y_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((yP s).setWidth 64) 16 := by
  refine ⟨yR s, ?_, Region.contains_self _ _⟩
  simp only [hp.wr, List.mem_append, List.mem_cons, or_true, true_or]

theorem Env.trans {s₀ s s' : State} (h : Env s₀ s) (h' : Env s s') : Env s₀ s' :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.saved r hr).trans (h.saved r hr)⟩

theorem prologue_ok (s₀ : State) (hp : GPre s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.prologue) s₀ fun s =>
      Inv s₀ 0 s ∧ s.cf = some (decide (nBlk s₀ < 8)) := by
  simp only [Impl.Gcm.X86.Pclmul.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 Impl.Gcm.X86.Pclmul.revMask s₀ (by decide))
    fun s₁ ⟨rev₁, f₁⟩ => ?_
  have e₁ := (Env.refl s₀).of_setup f₁
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 Impl.Gcm.X86.Pclmul.poly s₁ (by decide))
    fun s₂ ⟨poly₂, f₂⟩ => ?_
  have e₂ := e₁.of_setup f₂
  have rev₂ : s₂.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₂.xmm _ (by decide), rev₁]; rfl
  rw [show ([.mov .eax (.mem (argOp 0)), .movdquLoad .xmm7 (at_ .eax 0),
      .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) =
      ([.mov .eax (.mem (argOp 0))] : List Instr) ++
      [.movdquLoad .xmm7 (at_ .eax 0), .xop (.bin .pshufb .xmm7 .xmm0)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₂ 0 (by decide) .eax (by decide))
    fun s₃ ⟨ptr₃, e₃, _, x₃⟩ => ?_
  have hread₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.ea (at_ .eax 0)) 16 := by
    simp only [State.ea, at_, ptr₃, BitVec.add_zero, e₃.rd, e₃.wr]
    exact h_read hp
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .eax 0 s₃ (by decide) (by rw [x₃]; exact rev₂) hread₃)
    fun s₄ ⟨hash₄, f₄⟩ => ?_
  have e₄ := e₃.of_only f₄
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₄) fun s₅ ⟨hash₅, f₅⟩ => ?_
  have e₅ := e₄.of_setup f₅
  have rev₅ : s₅.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact rev₂
  have poly₅ : s₅.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact poly₂
  have hash₅' : x * φ (s₅.xmm .xmm3) = φ (H s₀) := by
    rw [hash₅, hash₄, e₃.mem]
    simp only [State.ea, at_, ptr₃, BitVec.add_zero]
  change WP isa (.block (([.mov .ecx (.mem (argOp 1))] : List Instr) ++
    [.movdquLoad .xmm2 (at_ .ecx 0), .xop (.bin .pshufb .xmm2 .xmm0),
      .mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .cmp .eax (.imm 8)])) s₅ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₅ 1 (by decide) .ecx (by decide))
    fun s₆ ⟨ptr₆, e₆, _, x₆⟩ => ?_
  have yread₆ : InRegions (s₆.rd ++ s₆.wr) (s₆.ea (at_ .ecx 0)) 16 := by
    simp only [State.ea, at_, ptr₆, BitVec.add_zero, e₆.rd, e₆.wr]
    exact y_read hp
  change WP isa (.block (([.movdquLoad .xmm2 (at_ .ecx 0),
    .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++
    [.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .cmp .eax (.imm 8)])) s₆ _
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm2 .ecx 0 s₆ (by decide) (by rw [x₆]; exact rev₅) yread₆)
    fun s₇ ⟨acc₇, f₇⟩ => ?_
  have e₇ := e₆.of_only f₇
  change WP isa (.block (([.mov .edx (.mem (argOp 2))] : List Instr) ++
    [.mov .eax (.mem (argOp 3)), .alu .cmp .eax (.imm 8)])) s₇ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₇ 2 (by decide) .edx (by decide))
    fun s₈ ⟨ptr₈, e₈, regs₈, x₈⟩ => ?_
  change WP isa (.block (([.mov .eax (.mem (argOp 3))] : List Instr) ++
    [.alu .cmp .eax (.imm 8)])) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₈ 3 (by decide) .eax (by decide))
    fun s₉ ⟨count₉, e₉, regs₉, x₉⟩ => ?_
  refine WP.mono (cmp8_ok s₉) fun s ⟨cf, ef, regs, xs⟩ => ?_
  constructor
  · refine ⟨e₉.trans ef, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regs, count₉, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [regs, regs₉ _ (by decide), ptr₈, Nat.mul_zero, BitVec.add_zero]
    · rw [regs, regs₉ _ (by decide), regs₈ _ (by decide), f₇.gpr, ptr₆]
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact rev₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact poly₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact hash₅'
    · rw [xs, x₉, x₈, acc₇, e₆.mem]
      simp only [State.ea, at_, ptr₆, BitVec.add_zero,
        Y, Proof.Gcm.ghashFrom_blocksAt_zero]
  · rw [cf, count₉]

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre dP nBlk dR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem data_read {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx 0)) 16 := by
  have hf := hp.fD
  have he : s.ea (at_ .edx 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega_using [hb, hf])
  rw [he, hi.env.rd, hi.env.wr, hp.rd]
  refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb, hf])⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

theorem xor_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm2 .xmm7)]) s fun s' =>
      s'.xmm .xmm2 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm2] s s' := by
  refine WP.of_runBlock ⟨s.setXmm .xmm2 (s.xmm .xmm2 ^^^ s.xmm .xmm7), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, XBinOp.eval, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro r hr
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]) s fun s' =>
      s'.gpr .eax = s.gpr .eax - 1 ∧ s'.gpr .edx = s.gpr .edx + 16 ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧ Env s s' ∧
      s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact (((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _ |>.setReg .eax _ (by decide)

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.body, List.append_assoc]
  rw [show ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) =
    ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++
    [.xop (.bin .pxor .xmm2 .xmm7)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .edx 0 s (by decide) hi.rev (data_read hp hi hb))
    fun s₁ ⟨input₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xor_ok s₁) fun s₂ ⟨acc₂, f₂⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  refine WP.mono (mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have env₃ := ((hi.env.of_only f₁).of_only f₂).of_only f₃
  have acc₃ : s₃.xmm .xmm2 = Y s₀ (i + 1) := by
    apply φ_inj
    have hin : s₁.xmm .xmm7 = Spec.Gcm.blockAt s₀.mem
        ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) := by
      rw [input₁, hi.env.mem]
      refine congrArg (Spec.Gcm.blockAt _) ?_
      simp only [State.ea, at_, hi.data, BitVec.add_zero]
      exact addr_eq (by have hf := hp.fD; omega_using [hb, hf])
    rw [mul₃, acc₂, hin, f₁.xmm _ (by decide), hi.acc]
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]
    rw [mul_assoc, mul_left_comm x, hi.hash]
    rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ Spec.Gcm.blockAt s₀.mem
      ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i))) (H s₀) from
      Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul]
  refine WP.mono (advance_ok s₃) fun s₄ ⟨count₄, data₄, zf₄, ef₄, out₄, xmm₄⟩ => ?_
  have regs₃ : s₃.gpr = s.gpr := f₃.gpr.trans (f₂.gpr.trans f₁.gpr)
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have count : s₃.gpr .eax - 1 = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [regs₃, hi.count, Wp.ofNat_pred (by omega_using [hb]), Nat.sub_sub]
  constructor
  · refine ⟨env₃.trans ef₄, by omega_using [hb], count₄.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [data₄, regs₃, hi.data, BitVec.add_assoc]
      change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
      rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega_using []]
    · rw [out₄, regs₃]; exact hi.out
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
    · rw [xmm₄, f₃.xmm _ (by decide)]; exact poly₂
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.hash
    · rw [xmm₄]; exact acc₃
  · rw [zf₄, count, Wp.ofNat_beq_zero (by omega_using [bound])]

end VG.Proof.Gcm.X86.Pclmul

end

/-! ## Eight blocks at a time

With eight blocks or more, `pows` writes the scratch buffer: `H'¹`, …, `H'⁸`,
`Y`, the reduction's constant, and the sums of the halves of the powers
(`Tab`). The blocks eight at a time (`body8`) keep `Y` there, so that the
memory differs from the entry state's in that buffer only (`KInv`). The
state after them, `s₁`, is one that satisfies the precondition too, with
the same `H`, `Y` and data (`Base`): the blocks one at a time (`body`) are
proven from `s₁`, whose memory they keep. -/

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP sP nBlk hR yR dR sR aR rR)
open VG.Impl.Gcm.X86.Pclmul (at_ argOp slot)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- The address of the slot `k` of the scratch buffer. -/
abbrev sA (s₀ : State) (k : Nat) : Addr := addr (sP s₀) (16 * k)

theorem slot_ea {s₀ s : State} (hc : s.gpr .ecx = sP s₀) (k : Nat) : s.ea (slot k) = sA s₀ k := by
  simp only [slot, at_, State.ea, hc, sA, addr]

theorem slot_in {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < 16) : (sR s₀).Contains (sA s₀ k) 16 :=
  Proof.Aes.X86.reg_contains hp.fS (by omega_using [hk]) (by decide)

theorem slot_wr {s₀ s : State} (hp : GPre s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (sA s₀ k) 16 := by
  rw [hw, hp.wr]
  exact ⟨sR s₀, by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true], slot_in hp hk⟩

theorem slot_rd {s₀ s : State} (hp : GPre s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (sA s₀ k) 16 :=
  Proof.Aes.X86.in_rd (slot_wr hp hw hk)

theorem slot_sep {s₀ : State} (hp : GPre s₀) {j k : Nat} (hj : j < 16) (hk : k < 16) (hne : j ≠ k) :
    Mem.Sep (sA s₀ j) (128 / 8) (sA s₀ k) (128 / 8) :=
  (Proof.Aes.X86.part_disj hp.fS (by omega_using [hj]) (by omega_using [hk])
    (by omega_using [hne])).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- An unaligned 16-byte load. -/
theorem ld_ok (r : XReg) (m : MemOp) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    WP isa (.block [.movdquLoad r m]) s fun s' =>
      s'.xmm r = s.mem.readW (s.ea m) 128 ∧ Only [r] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, hin,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _, rd_setXmm _ _ _, wr_setXmm _ _ _,
    fun a ha => ?_⟩
  exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using ha)

/-- An unaligned 16-byte store. -/
theorem st_ok (r : XReg) (m : MemOp) (s : State) (hin : InRegions s.wr (s.ea m) 16) :
    WP isa (.block [.movdquStore m r]) s fun s' =>
      s'.mem = s.mem.writeW (s.ea m) (s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, hin,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ### The powers -/

/-- While the powers are computed: memory differs from `s₀`'s in the scratch
buffer only, whose slots before `k` hold the powers, its slot 8 `y`, and its
slot 9 the reduction's constant. -/
structure PInv (s₀ : State) (g : Reg → BitVec 32) (y : BitVec 128) (k : Nat) (s : State) : Prop where
  frame : Frame [sR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : s.gpr = g
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  saved : s.mem.readW (sA s₀ 8) 128 = y
  const : s.mem.readW (sA s₀ 9) 128 = Impl.Gcm.X86.Pclmul.poly
  pow : ∀ j < k, x * φ (s.mem.readW (sA s₀ j) 128) = φ (H s₀) ^ (j + 1)

theorem mulSlots_ok {s₀ s : State} (hp : GPre s₀) {g : Reg → BitVec 32} {y : BitVec 128}
    (hc : g .ecx = sP s₀) {d a b : Nat} (hi : PInv s₀ g y d s) (ha : a < d) (hb : b < d) (hd : d < 8)
    (hab : a + b + 1 = d) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.mulSlots d a b)) s (PInv s₀ g y (d + 1)) := by
  have c₀ : s.gpr .ecx = sP s₀ := by rw [hi.gpr, hc]
  simp only [Impl.Gcm.X86.Pclmul.mulSlots, List.append_assoc]
  rw [WP.block_append_iff, block_one]
  refine WP.mono (ld_ok .xmm2 (slot a) s (by rw [slot_ea c₀]; exact slot_rd hp hi.wr (by omega_using [ha, hd])))
    fun s₁ ⟨v₁, f₁⟩ => ?_
  have c₁ : s₁.gpr .ecx = sP s₀ := by rw [f₁.gpr, c₀]
  refine WP.mono (ld_ok .xmm3 (slot b) s₁ (by
    rw [slot_ea c₁]; exact slot_rd hp (f₁.wr.trans hi.wr) (by omega_using [hb, hd])))
    fun s₂ ⟨v₂, f₂⟩ => ?_
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have c₃ : s₃.gpr .ecx = sP s₀ := by rw [f₃.gpr, f₂.gpr, c₁]
  have m₃ : s₃.mem = s.mem := f₃.mem.trans (f₂.mem.trans f₁.mem)
  have w₃ : s₃.wr = s₀.wr := f₃.wr.trans (f₂.wr.trans (f₁.wr.trans hi.wr))
  refine WP.mono (st_ok .xmm2 (slot d) s₃ (by rw [slot_ea c₃]; exact slot_wr hp w₃ (by omega_using [hd])))
    fun s₄ ⟨m₄, g₄, x₄, rd₄, wr₄⟩ => ?_
  rw [slot_ea c₃, m₃] at m₄
  have hpw : x * φ (s₃.xmm .xmm2) = φ (H s₀) ^ (d + 1) := by
    rw [mul₃, f₂.xmm .xmm2 (by decide), v₁, v₂, f₁.mem, slot_ea c₀, slot_ea c₁,
      show x * (x * φ (s.mem.readW (sA s₀ a) 128) * φ (s.mem.readW (sA s₀ b) 128)) =
        x * φ (s.mem.readW (sA s₀ a) 128) * (x * φ (s.mem.readW (sA s₀ b) 128)) by ring,
      hi.pow a ha, hi.pow b hb, ← pow_add]
    exact congrArg _ (by omega_using [hab])
  have other : ∀ j, j < 16 → j ≠ d → s₄.mem.readW (sA s₀ j) 128 = s.mem.readW (sA s₀ j) 128 :=
    fun j hj hne => by
      rw [m₄, Mem.readW_writeW_sep (slot_sep hp hj (by omega_using [hd]) hne) (by decide)]
  refine ⟨?_, rd₄.trans (f₃.rd.trans (f₂.rd.trans (f₁.rd.trans hi.rd))), wr₄.trans w₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₄]
    exact hi.frame.writeW (List.mem_singleton_self _) _ (slot_in hp (by omega_using [hd]))
  · rw [g₄, f₃.gpr, f₂.gpr, f₁.gpr]; exact hi.gpr
  · rw [x₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
  · rw [x₄, f₃.xmm _ (by decide)]; exact poly₂
  · rw [other 8 (by decide) (by omega_using [hd])]; exact hi.saved
  · rw [other 9 (by decide) (by omega_using [hd])]; exact hi.const
  · intro j hj
    by_cases hjd : j = d
    · rw [hjd, m₄, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      exact hpw
    · rw [other j (by omega_using [hj, hd]) hjd]
      exact hi.pow j (by omega_using [hj, hjd])

/-- The slot `10 + k / 2` holds the sum of the halves of the slot `k`, in its
quadword `k % 2`. -/
def HalfAt (s₀ : State) (m : Mem) (k : Nat) : Prop :=
  qword (m.readW (sA s₀ (10 + k / 2)) 128) (k % 2) = halfSum (m.readW (sA s₀ k) 128)

theorem hsum_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.hsum) s fun s' =>
      s'.xmm .xmm4 = halfSum (s.xmm .xmm3) ++ halfSum (s.xmm .xmm2) ∧ Only [.xmm4, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.hsum]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, eval_pxor, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · rw [← qword_swapXor, ← qword_swapXor]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2, ite_false]

theorem halves_ok {s₀ s : State} (hp : GPre s₀) {g : Reg → BitVec 32} {y : BitVec 128}
    (hc : g .ecx = sP s₀) {h : Nat} (hh : h < 4) (hi : PInv s₀ g y 8 s)
    (hv : ∀ k < 2 * h, HalfAt s₀ s.mem k) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.halves h)) s fun s' =>
      PInv s₀ g y 8 s' ∧ ∀ k < 2 * (h + 1), HalfAt s₀ s'.mem k := by
  have c₀ : s.gpr .ecx = sP s₀ := by rw [hi.gpr, hc]
  simp only [Impl.Gcm.X86.Pclmul.halves, List.append_assoc]
  rw [WP.block_append_iff, block_one]
  refine WP.mono (ld_ok .xmm2 (slot (2 * h)) s (by
    rw [slot_ea c₀]; exact slot_rd hp hi.wr (by omega_using [hh]))) fun s₁ ⟨v₁, f₁⟩ => ?_
  have c₁ : s₁.gpr .ecx = sP s₀ := by rw [f₁.gpr, c₀]
  refine WP.mono (ld_ok .xmm3 (slot (2 * h + 1)) s₁ (by
    rw [slot_ea c₁]; exact slot_rd hp (f₁.wr.trans hi.wr) (by omega_using [hh]))) fun s₂ ⟨v₂, f₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hsum_ok s₂) fun s₃ ⟨sum₃, f₃⟩ => ?_
  have c₃ : s₃.gpr .ecx = sP s₀ := by rw [f₃.gpr, f₂.gpr, c₁]
  have m₃ : s₃.mem = s.mem := f₃.mem.trans (f₂.mem.trans f₁.mem)
  have w₃ : s₃.wr = s₀.wr := f₃.wr.trans (f₂.wr.trans (f₁.wr.trans hi.wr))
  refine WP.mono (st_ok .xmm4 (slot (10 + h)) s₃ (by
    rw [slot_ea c₃]; exact slot_wr hp w₃ (by omega_using [hh]))) fun s₄ ⟨m₄, g₄, x₄, rd₄, wr₄⟩ => ?_
  rw [slot_ea c₃, m₃, sum₃, v₂, f₂.xmm .xmm2 (by decide), v₁, f₁.mem, slot_ea c₀, slot_ea c₁] at m₄
  have other : ∀ j, j < 10 → s₄.mem.readW (sA s₀ j) 128 = s.mem.readW (sA s₀ j) 128 := fun j hj => by
    rw [m₄, Mem.readW_writeW_sep (slot_sep hp (by omega_using [hj]) (by omega_using [hh])
      (by omega_using [hj])) (by decide)]
  refine ⟨⟨?_, rd₄.trans (f₃.rd.trans (f₂.rd.trans (f₁.rd.trans hi.rd))), wr₄.trans w₃, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [m₄]
    exact hi.frame.writeW (List.mem_singleton_self _) _ (slot_in hp (by omega_using [hh]))
  · rw [g₄, f₃.gpr, f₂.gpr, f₁.gpr]; exact hi.gpr
  · rw [x₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
  · rw [x₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  · rw [other 8 (by decide)]; exact hi.saved
  · rw [other 9 (by decide)]; exact hi.const
  · intro j hj
    rw [other j (by omega_using [hj])]; exact hi.pow j hj
  · intro k hk
    rcases (by omega_using [hk] : k < 2 * h ∨ k = 2 * h ∨ k = 2 * h + 1) with hlt | rfl | rfl
    · have hk' := hv k hlt
      unfold HalfAt at hk' ⊢
      rw [other k (by omega_using [hlt, hh]), m₄, Mem.readW_writeW_sep (slot_sep hp
        (by omega_using [hlt, hh]) (by omega_using [hh]) (by omega_using [hlt])) (by decide)]
      exact hk'
    · unfold HalfAt
      rw [other (2 * h) (by omega_using [hh]), show 2 * h / 2 = h by omega_using [],
        show 2 * h % 2 = 0 by omega_using [], m₄, Mem.readW_writeW_self _ _ 16 _ (by decide),
        qword_append_0]
    · unfold HalfAt
      rw [other (2 * h + 1) (by omega_using [hh]), show (2 * h + 1) / 2 = h by omega_using [],
        show (2 * h + 1) % 2 = 1 by omega_using [], m₄, Mem.readW_writeW_self _ _ 16 _ (by decide),
        qword_append_1]

/-! ### The scratch buffer after the powers -/

/-- The scratch buffer holds the powers, the reduction's constant and the
sums of the halves of the powers. -/
structure Tab (s₀ : State) (m : Mem) : Prop where
  pow : ∀ j < 8, x * φ (m.readW (sA s₀ j) 128) = φ (H s₀) ^ (j + 1)
  poly : m.readW (sA s₀ 9) 128 = Impl.Gcm.X86.Pclmul.poly
  half : ∀ k < 8, HalfAt s₀ m k

/-- A store of `Y`, in the slot 8, keeps the rest. -/
theorem Tab.store {s₀ : State} (hp : GPre s₀) {m : Mem} (h : Tab s₀ m) (v : BitVec 128) :
    Tab s₀ (m.writeW (sA s₀ 8) v) := by
  have other : ∀ j, j < 16 → j ≠ 8 →
      (m.writeW (sA s₀ 8) v).readW (sA s₀ j) 128 = m.readW (sA s₀ j) 128 :=
    fun j hj hne => Mem.readW_writeW_sep (slot_sep hp hj (by decide) hne) (by decide)
  refine ⟨fun j hj => ?_, ?_, fun k hk => ?_⟩
  · rw [other j (by omega_using [hj]) (by omega_using [hj])]; exact h.pow j hj
  · rw [other 9 (by decide) (by decide)]; exact h.poly
  · have hk' := h.half k hk
    unfold HalfAt at hk' ⊢
    rw [other k (by omega_using [hk]) (by omega_using [hk]),
      other (10 + k / 2) (by omega_using [hk]) (by omega_using [hk])]
    exact hk'

/-- Between the blocks of eight: memory differs from `s₀`'s in the scratch
buffer only, which holds the powers and what goes with them (`Tab`), and
`Y` after `i` blocks in its slot 8. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  frame : Frame [sR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  le : i ≤ nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  scr : s.gpr .ecx = sP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  tab : Tab s₀ s.mem
  acc : s.mem.readW (sA s₀ 8) 128 = Y s₀ i

theorem pows_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ 0 s) :
    WP isa (.block Impl.Gcm.X86.Pclmul.pows) s (KInv s₀ 0) := by
  simp only [Impl.Gcm.X86.Pclmul.pows, List.append_assoc]
  rw [WP.block_append_iff, block_one]
  refine WP.mono (movArg_ok hp hi.env 4 (by decide) .ecx (by decide)) fun t₁ ⟨c₁, e₁, r₁, x₁⟩ => ?_
  rw [block_one]
  refine WP.mono (st_ok .xmm2 (slot 8) t₁ (by rw [slot_ea c₁]; exact slot_wr hp e₁.wr (by decide)))
    fun t₂ ⟨m₂, g₂, x₂, rd₂, wr₂⟩ => ?_
  have c₂ : t₂.gpr .ecx = sP s₀ := by rw [g₂]; exact c₁
  rw [block_one]
  refine WP.mono (st_ok .xmm3 (slot 0) t₂ (by
    rw [slot_ea c₂]; exact slot_wr hp (wr₂.trans e₁.wr) (by decide)))
    fun t₃ ⟨m₃, g₃, x₃, rd₃, wr₃⟩ => ?_
  have c₃ : t₃.gpr .ecx = sP s₀ := by rw [g₃]; exact c₂
  refine WP.mono (st_ok .xmm1 (slot 9) t₃ (by
    rw [slot_ea c₃]; exact slot_wr hp (wr₃.trans (wr₂.trans e₁.wr)) (by decide)))
    fun t₄ ⟨m₄, g₄, x₄, rd₄, wr₄⟩ => ?_
  rw [slot_ea c₁, e₁.mem] at m₂
  rw [slot_ea c₂, m₂] at m₃
  rw [slot_ea c₃, m₃] at m₄
  have p₄ : PInv s₀ t₁.gpr (s.xmm .xmm2) 1 t₄ := by
    refine ⟨?_, rd₄.trans (rd₃.trans (rd₂.trans e₁.rd)), wr₄.trans (wr₃.trans (wr₂.trans e₁.wr)),
      g₄.trans (g₃.trans g₂), ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₄]
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_in hp (by decide))).writeW
        (List.mem_singleton_self _) _ (slot_in hp (by decide))).writeW
        (List.mem_singleton_self _) _ (slot_in hp (by decide))
    · rw [x₄, x₃, x₂, x₁]; exact hi.rev
    · rw [x₄, x₃, x₂, x₁]; exact hi.poly
    · rw [m₄, Mem.readW_writeW_sep (slot_sep hp (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (slot_sep hp (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self _ _ 16 _ (by decide), x₁]
    · rw [m₄, Mem.readW_writeW_self _ _ 16 _ (by decide), x₃, x₂, x₁]; exact hi.poly
    · intro j hj
      obtain rfl : j = 0 := by omega_using [hj]
      rw [m₄, Mem.readW_writeW_sep (slot_sep hp (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self _ _ 16 _ (by decide), x₂, x₁, hi.hash, pow_one]
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₄ (by decide) (by decide) (by decide) (by decide)) fun t₅ p₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₅ (by decide) (by decide) (by decide) (by decide)) fun t₆ p₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₆ (by decide) (by decide) (by decide) (by decide)) fun t₇ p₇ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₇ (by decide) (by decide) (by decide) (by decide)) fun t₈ p₈ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₈ (by decide) (by decide) (by decide) (by decide)) fun t₉ p₉ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₉ (by decide) (by decide) (by decide) (by decide)) fun t₁₀ p₁₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hp c₁ p₁₀ (by decide) (by decide) (by decide) (by decide)) fun t₁₁ p₁₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (halves_ok hp c₁ (h := 0) (by decide) p₁₁ (fun k hk => absurd hk (Nat.not_lt_zero k)))
    fun u₁ ⟨q₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (halves_ok hp c₁ (h := 1) (by decide) q₁ h₁) fun u₂ ⟨q₂, h₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (halves_ok hp c₁ (h := 2) (by decide) q₂ h₂) fun u₃ ⟨q₃, h₃⟩ => ?_
  refine WP.mono (halves_ok hp c₁ (h := 3) (by decide) q₃ h₃) fun u₄ ⟨q₄, h₄⟩ => ?_
  exact ⟨q₄.frame, q₄.rd, q₄.wr, fun r hr => by
      rw [q₄.gpr, r₁ r (by rintro rfl; exact absurd hr (by decide))]; exact hi.env.saved r hr,
    Nat.zero_le _, by rw [q₄.gpr, r₁ .eax (by decide)]; exact hi.count,
    by rw [q₄.gpr, r₁ .edx (by decide)]; exact hi.data, by rw [q₄.gpr]; exact c₁, q₄.rev,
    ⟨q₄.pow, q₄.const, h₄⟩, by rw [q₄.saved]; exact hi.acc⟩

/-! ### The state after the blocks of eight -/

/-- `s₁` is `s₀` but for the scratch buffer (and the registers that are not
callee-saved). -/
structure Base (s₀ s₁ : State) : Prop where
  frame : Frame [sR s₀] s₀.mem s₁.mem
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r

theorem Base.refl (s : State) : Base s s := ⟨Frame.refl _ _, rfl, rfl, fun _ _ => rfl⟩

theorem Base.sp {s₀ s₁ : State} (h : Base s₀ s₁) : s₁.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Base.arg_eq {s₀ s₁ : State} (h : Base s₀ s₁) (hp : GPre s₀) {i : Nat} (hi : i < 5) :
    arg s₁ i = arg s₀ i := by
  simp only [arg, argAddr, h.sp]
  exact h.frame.readW (r := aR s₀)
    (Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20) hp.fSp (by decide) (by omega_using [])
      (by omega_using [hi]) (by decide))
    (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hp.aS) (by decide)

/-- A block outside the scratch buffer is what it was. -/
theorem Base.block_eq {s₀ s₁ : State} (h : Base s₀ s₁) {p : Addr}
    (hd : (⟨p, 16⟩ : Region).Disjoint (sR s₀)) : blockAt s₁.mem p = blockAt s₀.mem p :=
  Proof.Gcm.blockAt_congr fun _ hi => h.frame.bytes (R := ⟨p, 16⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (show (16 : Nat) ≤ 2 ^ 64 by decide) hi

theorem Base.blocks_eq {s₀ s₁ : State} (h : Base s₀ s₁) {p : Addr} {n i : Nat}
    (hd : (⟨p, 16 * n⟩ : Region).Disjoint (sR s₀)) (hn : 16 * n ≤ 2 ^ 64) (hi : i ≤ n) :
    blocksAt s₁.mem p i = blocksAt s₀.mem p i := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => Proof.Gcm.blockAt_congr fun k hk => ?_
  have hj' := List.mem_range.mp hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.frame.bytes (R := ⟨p, 16 * n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hn
    (by show 16 * j + k < 16 * n; omega_using [hj', hk, hi])

theorem Base.H_eq {s₀ s₁ : State} (h : Base s₀ s₁) (hp : GPre s₀) : H s₁ = H s₀ := by
  show blockAt s₁.mem ((arg s₁ 0).setWidth 64) = blockAt s₀.mem ((arg s₀ 0).setWidth 64)
  rw [h.arg_eq hp (by decide)]
  exact h.block_eq hp.dHS

theorem Base.Y_eq {s₀ s₁ : State} (h : Base s₀ s₁) (hp : GPre s₀) {i : Nat} (hi : i ≤ nBlk s₀) :
    Y s₁ i = Y s₀ i := by
  show ghashFrom (H s₁) (blockAt s₁.mem ((arg s₁ 1).setWidth 64))
    (blocksAt s₁.mem ((arg s₁ 2).setWidth 64) i) = _
  rw [h.H_eq hp, h.arg_eq hp (by decide), h.arg_eq hp (by decide), h.block_eq hp.dYS,
    h.blocks_eq hp.dDS (by have := hp.fD; omega_using [this]) hi]

theorem Base.gpre {s₀ s₁ : State} (h : Base s₀ s₁) (hp : GPre s₀) : GPre s₁ := by
  have e0 := h.arg_eq hp (show 0 < 5 by decide)
  have e1 := h.arg_eq hp (show 1 < 5 by decide)
  have e2 := h.arg_eq hp (show 2 < 5 by decide)
  have e3 := h.arg_eq hp (show 3 < 5 by decide)
  have e4 := h.arg_eq hp (show 4 < 5 by decide)
  have ea : argAddr s₁ 0 = argAddr s₀ 0 := by simp only [argAddr, h.sp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hR, yR, dR, sR, aR, rR, hP, yP, dP, sP, nBlk, h.rd, h.wr, h.sp, e0, e1, e2, e3, e4, ea]
  exacts [hp.rd, hp.wr, hp.dHY, hp.dHS, hp.dYD, hp.dYS, hp.dDS, hp.aY, hp.aS, hp.rY, hp.rS, hp.fH, hp.fY,
    hp.fD, hp.fS, hp.fSp]

/-- The contract from `s₁` is the contract from `s₀`. -/
theorem Base.finish {s₀ s₁ s' : State} (h : Base s₀ s₁) (hp : GPre s₀)
    (hq : abiPreserved s₁ s' ∧ Proof.Gcm.ghashX86.post s₁ s') :
    abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  obtain ⟨⟨hs, hr⟩, hpost⟩ := hq
  refine ⟨⟨fun r hr' => (hs r hr').trans (h.saved r hr'), ?_⟩, ?_⟩
  · rw [h.sp] at hr
    rw [hr]
    exact h.frame.readW (r := rR s₀) (Region.contains_self _ _)
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hp.rS) (by decide)
  · simp only [Proof.Gcm.ghashX86] at hpost ⊢
    rw [h.arg_eq hp (show 0 < 5 by decide), h.arg_eq hp (show 1 < 5 by decide),
      h.arg_eq hp (show 2 < 5 by decide), h.arg_eq hp (show 3 < 5 by decide)] at hpost
    rw [hpost, h.block_eq hp.dHS, h.block_eq hp.dYS,
      h.blocks_eq hp.dDS (by have := hp.fD; omega_using [this]) (Nat.le_refl _)]

/-! ### Eight blocks -/

/-- The block `j` of the data. -/
abbrev blk (s₀ : State) (j : Nat) : Block :=
  blockAt s₀.mem ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j))

/-- The address of block `i + j`, with block `i` in `edx`, and that it may be
read. -/
theorem data_read8 {s₁ s : State} (hp : GPre s₁) {i : Nat} (j : Nat) (hrd : s.rd = s₁.rd)
    (hwr : s.wr = s₁.wr) (hd : s.gpr .edx = dP s₁ + BitVec.ofNat 32 (16 * i)) (hb : i + j < nBlk s₁) :
    s.ea (at_ .edx (16 * j)) = (dP s₁).setWidth 64 + BitVec.ofNat 64 (16 * (i + j)) ∧
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx (16 * j))) 16 := by
  have hf := hp.fD
  have he : s.ea (at_ .edx (16 * j)) = (dP s₁).setWidth 64 + BitVec.ofNat 64 (16 * (i + j)) := by
    simp only [State.ea, at_, hd]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * i + 16 * j = 16 * (i + j) by omega_using []]
    exact addr_eq (by omega_using [hb, hf])
  refine ⟨he, ?_⟩
  rw [he, hrd, hwr, hp.rd]
  refine ⟨dR s₁, ?_, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb, hf])⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

/-- A block of the data is what it was, in a memory that differs in the
scratch buffer only. -/
theorem data_block {s₀ : State} (hp : GPre s₀) {m : Mem} (hf : Frame [sR s₀] s₀.mem m) {j : Nat}
    (hj : j < nBlk s₀) :
    blockAt m ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) = blk s₀ j := by
  have hd := hp.fD
  refine Proof.Gcm.blockAt_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hf.bytes (R := ⟨(dP s₀).setWidth 64, 16 * nBlk s₀⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dDS)
    (by show 16 * nBlk s₀ ≤ 2 ^ 64; omega_using [hd])
    (by show 16 * j + k < 16 * nBlk s₀; omega_using [hj, hk])

theorem klohi_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.klohi) s fun s' =>
      s'.xmm .xmm4 = s.xmm .xmm4 ^^^ pclmul (s.xmm .xmm2) (s.xmm .xmm3) 0x00 ∧
      s'.xmm .xmm6 = s.xmm .xmm6 ^^^ pclmul (s.xmm .xmm2) (s.xmm .xmm3) 0x11 ∧
      s'.xmm .xmm1 = shufDwords (s.xmm .xmm2) 0x4e ^^^ s.xmm .xmm2 ∧
      Only [.xmm7, .xmm4, .xmm1, .xmm2, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.klohi]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem kmid_ok (s : State) (sel : BitVec 8) :
    WP isa (.block [.xop (.pclmulqdq .xmm1 .xmm3 sel), .xop (.bin .pxor .xmm5 .xmm1)]) s fun s' =>
      s'.xmm .xmm5 = s.xmm .xmm5 ^^^ pclmul (s.xmm .xmm1) (s.xmm .xmm3) sel ∧
      Only [.xmm1, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, eval_pxor, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2, ite_false]

/-- A block times the power in the slot `k`: its three products, added. -/
theorem kblock_ok {s₀ s : State} (hp : GPre s₀) {k : Nat} (hk : k < 8) (hc : s.gpr .ecx = sP s₀)
    (hw : s.wr = s₀.wr) (ht : Tab s₀ s.mem) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.kblock k)) s fun s' =>
      prod s' = (prod s).kacc (s.xmm .xmm2) (s.mem.readW (sA s₀ k) 128) ∧ Only work s s' := by
  simp only [Impl.Gcm.X86.Pclmul.kblock, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm3 (slot k) s (by rw [slot_ea hc]; exact slot_rd hp hw (by omega_using [hk])))
    fun s₁ ⟨v₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (klohi_ok s₁) fun s₂ ⟨lo₂, hi₂, sum₂, f₂⟩ => ?_
  have c₂ : s₂.gpr .ecx = sP s₀ := by rw [f₂.gpr, f₁.gpr]; exact hc
  rw [block_one]
  refine WP.mono (ld_ok .xmm3 (slot (10 + k / 2)) s₂ (by
    rw [slot_ea c₂]; exact slot_rd hp (f₂.wr.trans (f₁.wr.trans hw)) (by omega_using [hk])))
    fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (kmid_ok s₃ (Impl.Gcm.X86.Pclmul.halfSel k)) fun s₄ ⟨mid₄, f₄⟩ =>
    ⟨?_, ((f₁.work.seq f₂.work).seq f₃.work).seq f₄.work⟩
  have e4 : s₄.xmm .xmm4 = s.xmm .xmm4 ^^^ pclmul (s.xmm .xmm2) (s.mem.readW (sA s₀ k) 128) 0x00 := by
    rw [f₄.xmm _ (by decide), f₃.xmm _ (by decide), lo₂, f₁.xmm .xmm4 (by decide),
      f₁.xmm .xmm2 (by decide), v₁, slot_ea hc]
  have e6 : s₄.xmm .xmm6 = s.xmm .xmm6 ^^^ pclmul (s.xmm .xmm2) (s.mem.readW (sA s₀ k) 128) 0x11 := by
    rw [f₄.xmm _ (by decide), f₃.xmm _ (by decide), hi₂, f₁.xmm .xmm6 (by decide),
      f₁.xmm .xmm2 (by decide), v₁, slot_ea hc]
  have e5 : s₄.xmm .xmm5 = s.xmm .xmm5 ^^^
      clmul (halfSum (s.xmm .xmm2)) (halfSum (s.mem.readW (sA s₀ k) 128)) := by
    have hk' := ht.half k hk
    unfold HalfAt at hk'
    rw [mid₄, f₃.xmm .xmm5 (by decide), f₂.xmm .xmm5 (by decide), f₁.xmm .xmm5 (by decide),
      f₃.xmm .xmm1 (by decide), sum₂, v₃, pclmul_halfSel, qword_swapXor, slot_ea c₂, f₂.mem, f₁.mem,
      hk', f₁.xmm .xmm2 (by decide)]
  simp only [prod, Prod.kacc, e4, e5, e6]

/-- A block of eight but its first: its product with its power, added. -/
theorem later_ok {s₀ s t : State} (hp : GPre s₀) {i : Nat} (hi : KInv s₀ i s) (o : Only work s t)
    (j k : Nat) (hjk : j + k = 7) (hb : i + j < nBlk s₀) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.later j)) t fun t' =>
      Only work s t' ∧ prod t' = (prod t).kacc (blk s₀ (i + j)) (s.mem.readW (sA s₀ k) 128) := by
  have he : 7 - j = k := by omega_using [hjk]
  simp only [Impl.Gcm.X86.Pclmul.later, he]
  rw [WP.block_append_iff]
  obtain ⟨ea, hin⟩ := data_read8 hp j (o.rd.trans hi.rd) (o.wr.trans hi.wr)
    (by rw [o.gpr]; exact hi.data) hb
  refine WP.mono (ldrev_ok .xmm2 .edx (16 * j) t (by decide)
    (by rw [o.xmm _ (by decide)]; exact hi.rev) hin) fun t₁ ⟨in₁, f₁⟩ => ?_
  have o₁ := o.seq f₁.work
  refine WP.mono (kblock_ok hp (k := k) (by omega_using [hjk]) (by rw [o₁.gpr]; exact hi.scr)
    (o₁.wr.trans hi.wr) (by rw [o₁.mem]; exact hi.tab)) fun t₂ ⟨p₂, f₂⟩ => ⟨o₁.seq f₂, ?_⟩
  rw [p₂, prod_only f₁, in₁, ea, f₁.mem, o.mem, data_block hp hi.frame hb]

/-- The first block of eight, with `Y`: its product with `H'⁸`, added. -/
theorem last_ok {s₀ s t : State} (hp : GPre s₀) {i : Nat} (hi : KInv s₀ i s) (o : Only work s t)
    (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.last) t fun t' =>
      Only work s t' ∧
      prod t' = (prod t).kacc (blk s₀ i ^^^ Y s₀ i) (s.mem.readW (sA s₀ 7) 128) := by
  simp only [Impl.Gcm.X86.Pclmul.last, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨ea, hin⟩ := data_read8 hp 0 (o.rd.trans hi.rd) (o.wr.trans hi.wr)
    (by rw [o.gpr]; exact hi.data) (by omega_using [hb])
  rw [Nat.mul_zero] at ea hin
  rw [Nat.add_zero] at ea
  refine WP.mono (ldrev_ok .xmm2 .edx 0 t (by decide)
    (by rw [o.xmm _ (by decide)]; exact hi.rev) hin) fun t₁ ⟨in₁, f₁⟩ => ?_
  have o₁ := o.seq f₁.work
  have c₁ : t₁.gpr .ecx = sP s₀ := by rw [o₁.gpr]; exact hi.scr
  rw [WP.block_append_iff, block_one]
  refine WP.mono (ld_ok .xmm3 (slot 8) t₁ (by
    rw [slot_ea c₁]; exact slot_rd hp (o₁.wr.trans hi.wr) (by decide))) fun t₂ ⟨v₂, f₂⟩ => ?_
  have o₂ := o₁.seq f₂.work
  refine WP.mono (bin_ok .pxor .xmm2 .xmm3 t₂) fun t₃ ⟨v₃, f₃⟩ => ?_
  have o₃ := o₂.seq f₃.work
  refine WP.mono (kblock_ok hp (k := 7) (by decide) (by rw [o₃.gpr]; exact hi.scr)
    (o₃.wr.trans hi.wr) (by rw [o₃.mem]; exact hi.tab)) fun t₄ ⟨p₄, f₄⟩ => ⟨o₃.seq f₄, ?_⟩
  rw [p₄, prod_only f₃, prod_only f₂, prod_only f₁, v₃, eval_pxor, v₂, f₂.xmm .xmm2 (by decide), in₁, ea,
    slot_ea c₁, f₁.mem, o.mem, o₃.mem, data_block hp hi.frame hb, hi.acc]

theorem kmiddle_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.kmiddle) s fun s' =>
      s'.xmm .xmm4 = s.xmm .xmm4 ^^^ (s.xmm .xmm5 ^^^ s.xmm .xmm4 ^^^ s.xmm .xmm6) <<< 64 ∧
      s'.xmm .xmm6 = s.xmm .xmm6 ^^^ (s.xmm .xmm5 ^^^ s.xmm .xmm4 ^^^ s.xmm .xmm6) >>> 64 ∧
      Only [.xmm5, .xmm7, .xmm6, .xmm4] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.kmiddle]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, eval_pxor, eval_movdqa, psrldq8, pslldq8, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem kfold_ok (s : State) (h1 : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.kfold) s fun s' =>
      s'.xmm .xmm4 = fold (s.xmm .xmm4) ∧ Only [.xmm5, .xmm4] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.kfold]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, eval_pxor, eval_movdqa, h1, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2, ite_false]

/-- The sum of the eight products, reduced, into `xmm6` and the slot 8. -/
theorem kreduce_ok {s₀ t : State} (hp : GPre s₀) (hc : t.gpr .ecx = sP s₀) (hw : t.wr = s₀.wr)
    (hk : t.mem.readW (sA s₀ 9) 128 = Impl.Gcm.X86.Pclmul.poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.kreduce) t fun t' =>
      t'.xmm .xmm6 = reduce (prod t).kfix ∧ t'.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly ∧
      t'.mem = t.mem.writeW (sA s₀ 8) (reduce (prod t).kfix) ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ t'.xmm .xmm0 = t.xmm .xmm0 := by
  simp only [Impl.Gcm.X86.Pclmul.kreduce, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (kmiddle_ok t) fun t₁ ⟨lo₁, hi₁, f₁⟩ => ?_
  have c₁ : t₁.gpr .ecx = sP s₀ := by rw [f₁.gpr]; exact hc
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm1 (slot 9) t₁ (by
    rw [slot_ea c₁]; exact slot_rd hp (f₁.wr.trans hw) (by decide))) fun t₂ ⟨v₂, f₂⟩ => ?_
  have p₂ : t₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by rw [v₂, slot_ea c₁, f₁.mem]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (kfold_ok t₂ p₂) fun t₃ ⟨v₃, f₃⟩ => ?_
  have p₃ : t₃.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by rw [f₃.xmm _ (by decide)]; exact p₂
  rw [WP.block_append_iff]
  refine WP.mono (kfold_ok t₃ p₃) fun t₄ ⟨v₄, f₄⟩ => ?_
  rw [block_one]
  refine WP.mono (bin_ok .pxor .xmm6 .xmm4 t₄) fun t₅ ⟨v₅, f₅⟩ => ?_
  have e₅ : t₅.xmm .xmm6 = reduce (prod t).kfix := by
    rw [v₅, eval_pxor, v₄, v₃, f₄.xmm .xmm6 (by decide), f₃.xmm .xmm6 (by decide),
      f₂.xmm .xmm6 (by decide), f₂.xmm .xmm4 (by decide), hi₁, lo₁]
    rfl
  have c₅ : t₅.gpr .ecx = sP s₀ := by rw [f₅.gpr, f₄.gpr, f₃.gpr, f₂.gpr]; exact c₁
  have m₅ : t₅.mem = t.mem := f₅.mem.trans (f₄.mem.trans (f₃.mem.trans (f₂.mem.trans f₁.mem)))
  have w₅ : t₅.wr = t.wr := f₅.wr.trans (f₄.wr.trans (f₃.wr.trans (f₂.wr.trans f₁.wr)))
  refine WP.mono (st_ok .xmm6 (slot 8) t₅ (by
    rw [slot_ea c₅]; exact slot_wr hp (w₅.trans hw) (by decide))) fun t₆ ⟨m₆, g₆, x₆, rd₆, wr₆⟩ => ?_
  refine ⟨by rw [x₆]; exact e₅, ?_, ?_, ?_, ?_, wr₆.trans w₅, ?_⟩
  · rw [x₆, f₅.xmm _ (by decide), f₄.xmm _ (by decide)]; exact p₃
  · rw [m₆, slot_ea c₅, m₅, e₅]
  · rw [g₆, f₅.gpr, f₄.gpr, f₃.gpr, f₂.gpr, f₁.gpr]
  · rw [rd₆, f₅.rd, f₄.rd, f₃.rd, f₂.rd, f₁.rd]
  · rw [x₆, f₅.xmm _ (by decide), f₄.xmm _ (by decide), f₃.xmm _ (by decide), f₂.xmm _ (by decide),
      f₁.xmm _ (by decide)]

theorem φ_Y_succ (s₀ : State) (i : Nat) :
    φ (Y s₀ (i + 1)) = (φ (Y s₀ i) + φ (blk s₀ i)) * φ (H s₀) := by
  rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ blk s₀ i) (H s₀) from
    Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul, φ_xor]

/-- `Y` after eight more blocks. -/
theorem φ_Y8 (s₀ : State) (i : Nat) :
    φ (Y s₀ (i + 8)) =
      ((((((((φ (Y s₀ i) + φ (blk s₀ i)) * φ (H s₀) + φ (blk s₀ (i + 1))) * φ (H s₀) +
        φ (blk s₀ (i + 2))) * φ (H s₀) + φ (blk s₀ (i + 3))) * φ (H s₀) +
        φ (blk s₀ (i + 4))) * φ (H s₀) + φ (blk s₀ (i + 5))) * φ (H s₀) +
        φ (blk s₀ (i + 6))) * φ (H s₀) + φ (blk s₀ (i + 7))) * φ (H s₀) := by
  have e7 : φ (Y s₀ (i + 8)) = (φ (Y s₀ (i + 7)) + φ (blk s₀ (i + 7))) * φ (H s₀) := φ_Y_succ s₀ (i + 7)
  have e6 : φ (Y s₀ (i + 7)) = (φ (Y s₀ (i + 6)) + φ (blk s₀ (i + 6))) * φ (H s₀) := φ_Y_succ s₀ (i + 6)
  have e5 : φ (Y s₀ (i + 6)) = (φ (Y s₀ (i + 5)) + φ (blk s₀ (i + 5))) * φ (H s₀) := φ_Y_succ s₀ (i + 5)
  have e4 : φ (Y s₀ (i + 5)) = (φ (Y s₀ (i + 4)) + φ (blk s₀ (i + 4))) * φ (H s₀) := φ_Y_succ s₀ (i + 4)
  have e3 : φ (Y s₀ (i + 4)) = (φ (Y s₀ (i + 3)) + φ (blk s₀ (i + 3))) * φ (H s₀) := φ_Y_succ s₀ (i + 3)
  have e2 : φ (Y s₀ (i + 3)) = (φ (Y s₀ (i + 2)) + φ (blk s₀ (i + 2))) * φ (H s₀) := φ_Y_succ s₀ (i + 2)
  have e1 : φ (Y s₀ (i + 2)) = (φ (Y s₀ (i + 1)) + φ (blk s₀ (i + 1))) * φ (H s₀) := φ_Y_succ s₀ (i + 1)
  rw [e7, e6, e5, e4, e3, e2, e1, φ_Y_succ s₀ i]

theorem advance8_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 128), .alu .sub .eax (.imm 8), .alu .cmp .eax (.imm 8)]) s
      fun s' => s'.gpr .eax = s.gpr .eax - 8 ∧ s'.gpr .edx = s.gpr .edx + 128 ∧
        s'.cf = some (decide ((s.gpr .eax - 8).toNat < 8)) ∧ Env s s' ∧
        s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact ((((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _
    |>.setReg .eax _ (by decide)).arithFlags _ _ _

theorem body8_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : KInv s₀ i s)
    (hb : i + 8 ≤ nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body8) s fun s' =>
      KInv s₀ (i + 8) s' ∧ s'.xmm .xmm6 = Y s₀ (i + 8) ∧
      s'.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly ∧
      s'.cf = some (decide (nBlk s₀ - (i + 8) < 8)) := by
  simp only [Impl.Gcm.X86.Pclmul.body8, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun t₀ ⟨p₀, f₀⟩ => ?_
  have o₀ := f₀.work
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₀ 1 6 (by decide) (by omega_using [hb])) fun t₁ ⟨o₁, p₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₁ 2 5 (by decide) (by omega_using [hb])) fun t₂ ⟨o₂, p₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₂ 3 4 (by decide) (by omega_using [hb])) fun t₃ ⟨o₃, p₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₃ 4 3 (by decide) (by omega_using [hb])) fun t₄ ⟨o₄, p₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₄ 5 2 (by decide) (by omega_using [hb])) fun t₅ ⟨o₅, p₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₅ 6 1 (by decide) (by omega_using [hb])) fun t₆ ⟨o₆, p₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (later_ok hp hi o₆ 7 0 (by decide) (by omega_using [hb])) fun t₇ ⟨o₇, p₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (last_ok hp hi o₇ (by omega_using [hb])) fun t₈ ⟨o₈, p₈⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (kreduce_ok hp (by rw [o₈.gpr]; exact hi.scr) (o₈.wr.trans hi.wr)
    (by rw [o₈.mem]; exact hi.tab.poly)) fun t₉ ⟨r₉, k₉, m₉, g₉, rd₉, wr₉, x₉⟩ => ?_
  refine WP.mono (advance8_ok t₉) fun t ⟨count, data, cf, ef, out, xs⟩ => ?_
  have val : reduce (prod t₈).kfix = Y s₀ (i + 8) := by
    have e : ∀ (v : Q) (k : Nat), k < 8 →
        x * v * φ (s.mem.readW (sA s₀ k) 128) = v * φ (H s₀) ^ (k + 1) :=
      fun v k hk => by rw [← hi.tab.pow k hk]; ring
    apply φ_inj
    rw [φ_reduce, p₈, Prod.val_kacc, p₇, Prod.val_kacc, p₆, Prod.val_kacc, p₅, Prod.val_kacc, p₄,
      Prod.val_kacc, p₃, Prod.val_kacc, p₂, Prod.val_kacc, p₁, Prod.val_kacc, p₀, Prod.kfix_zero, φ_Y8,
      φ_xor, e _ 7 (by decide), e _ 6 (by decide), e _ 5 (by decide), e _ 4 (by decide),
      e _ 3 (by decide), e _ 2 (by decide), e _ 1 (by decide), e _ 0 (by decide)]
    ring
  have regs₉ : t₉.gpr = s.gpr := g₉.trans o₈.gpr
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have cnt : t₉.gpr .eax - 8 = BitVec.ofNat 32 (nBlk s₀ - (i + 8)) := by
    rw [regs₉, hi.count]
    exact (Wp.sub_ofNat (b := 8) (by omega_using [hb])).trans (congrArg _ (by omega_using []))
  have mem : t.mem = s.mem.writeW (sA s₀ 8) (Y s₀ (i + 8)) := by rw [ef.mem, m₉, o₈.mem, val]
  refine ⟨⟨?_, ef.rd.trans (rd₉.trans (o₈.rd.trans hi.rd)), ef.wr.trans (wr₉.trans (o₈.wr.trans hi.wr)),
    ?_, hb, count.trans cnt, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [mem]
    exact hi.frame.writeW (List.mem_singleton_self _) _ (slot_in hp (by decide))
  · intro r hr
    rw [ef.saved r hr, regs₉]; exact hi.saved r hr
  · rw [data, regs₉, hi.data, BitVec.add_assoc]
    change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 128) = _
    rw [← BitVec.ofNat_add, show 16 * i + 128 = 16 * (i + 8) by omega_using []]
  · rw [out, regs₉]; exact hi.scr
  · rw [xs, x₉, o₈.xmm _ (by decide)]; exact hi.rev
  · rw [mem]; exact hi.tab.store hp _
  · rw [mem]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  · rw [xs, r₉, val]
  · rw [xs]; exact k₉
  · rw [cf, cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]

theorem blocks8_ok {s₀ s : State} (hp : GPre s₀) (hi : KInv s₀ 0 s) (hn : 8 ≤ nBlk s₀) :
    WP isa (.loop (.block Impl.Gcm.X86.Pclmul.body8) .ae) s fun s' =>
      ∃ i, KInv s₀ i s' ∧ s'.xmm .xmm6 = Y s₀ i ∧ s'.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = nBlk s₀ - i ∧ i + 8 ≤ nBlk s₀ ∧ KInv s₀ i s)
    (fun k s ⟨i, hk, hb, hs⟩ => WP.mono (body8_ok hp hs hb) fun s' ⟨inv, h6, h1, c⟩ => ?_)
    (nBlk s₀) s ⟨0, rfl, hn, hi⟩
  by_cases hl : nBlk s₀ - (i + 8) < 8
  · exact .inl ⟨by simp [X86.eval, c, hl], i + 8, inv, h6, h1⟩
  · exact .inr ⟨by simp [X86.eval, c, hl], nBlk s₀ - (i + 8), by omega_using [hk, hb], i + 8, rfl,
      by omega_using [hb, hl], inv⟩

/-- After the blocks of eight: the state before `y` goes back into `ecx` is
one the blocks left are proven from. -/
theorem after8_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : KInv s₀ i s)
    (hy : s.xmm .xmm6 = Y s₀ i) (h1 : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.after8) s fun s' =>
      ∃ s₁ i, Base s₀ s₁ ∧ GPre s₁ ∧ Inv s₁ i s' := by
  simp only [Impl.Gcm.X86.Pclmul.after8]
  rw [block_one]
  refine WP.mono (bin_ok .movdqa .xmm2 .xmm6 s) fun t₁ ⟨v₁, f₁⟩ => ?_
  have c₁ : t₁.gpr .ecx = sP s₀ := by rw [f₁.gpr]; exact hi.scr
  rw [block_one]
  refine WP.mono (ld_ok .xmm3 (slot 0) t₁ (by
    rw [slot_ea c₁]; exact slot_rd hp (f₁.wr.trans hi.wr) (by decide))) fun t₂ ⟨v₂, f₂⟩ => ?_
  have o := f₁.trans f₂
  have hb : Base s₀ t₂ := ⟨by rw [o.mem]; exact hi.frame, o.rd.trans hi.rd, o.wr.trans hi.wr,
    fun r hr => by rw [o.gpr]; exact hi.saved r hr⟩
  have hp₂ := hb.gpre hp
  refine WP.mono (movArg_ok hp₂ (Env.refl t₂) 1 (by decide) .ecx (by decide))
    fun s₃ ⟨c₃, e₃, r₃, x₃⟩ => ?_
  refine ⟨t₂, i, hb, hp₂, e₃, ?_, ?_, ?_, c₃, ?_, ?_, ?_, ?_⟩
  · show i ≤ (arg t₂ 3).toNat
    rw [hb.arg_eq hp (by decide)]; exact hi.le
  · rw [r₃ _ (by decide), o.gpr, hi.count]
    show _ = BitVec.ofNat 32 ((arg t₂ 3).toNat - i)
    rw [hb.arg_eq hp (by decide)]
  · rw [r₃ _ (by decide), o.gpr, hi.data]
    show _ = arg t₂ 2 + _
    rw [hb.arg_eq hp (by decide)]
  · rw [x₃, o.xmm _ (by decide)]; exact hi.rev
  · rw [x₃, o.xmm _ (by decide)]; exact h1
  · rw [x₃, v₂, slot_ea c₁, f₁.mem, hb.H_eq hp]
    exact (hi.tab.pow 0 (by decide)).trans (pow_one _)
  · rw [x₃, f₂.xmm .xmm2 (by decide), v₁, eval_movdqa, hy]
    exact (hb.Y_eq hp hi.le).symm

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
open VG.Impl.Gcm.X86.Pclmul (at_ argOp)

theorem blocks_ok {s₀ s : State} (hp : GPre s₀) {i₀ : Nat} (hi : Inv s₀ i₀ s) (hn : i₀ < nBlk s₀) :
    WP isa (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne) s (Inv s₀ (nBlk s₀)) := by
  refine WP.loop (M := isa) (fun k s => ∃ i,
    k = nBlk s₀ - i ∧ i < nBlk s₀ ∧ Inv s₀ i s)
    (fun k s ⟨i, hk, hb, hs⟩ => WP.mono (body_ok hp hs hb) fun s' ⟨inv, z⟩ => ?_)
    (nBlk s₀ - i₀) s ⟨i₀, rfl, hn, hi⟩
  by_cases hl : i + 1 = nBlk s₀
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at inv; exact inv
  · exact .inr ⟨by simp [X86.eval, z]; omega_using [hb, hl],
      nBlk s₀ - (i + 1), by omega_using [hk, hb], i + 1, rfl, by omega_using [hb, hl], inv⟩

theorem epilogue_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ (nBlk s₀) s) :
    WP isa (.block Impl.Gcm.X86.Pclmul.epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  have writable : InRegions s.wr ((yP s₀).setWidth 64) 16 := by
    rw [hi.env.wr, hp.wr]
    exact ⟨yR s₀, by simp, Region.contains_self _ _⟩
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.epilogue, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.store128, gpr_setXmm, wr_setXmm, State.ea, at_, hi.out, BitVec.add_zero, writable,
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

/-- After `cmp eax, 8`: the blocks eight at a time, if there are eight, and a
state `s₁` that is `s₀` but for the scratch buffer. -/
theorem groups_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ 0 s)
    (c : s.cf = some (decide (nBlk s₀ < 8))) :
    WP isa (.ite .b (.block []) (.seq (.block Impl.Gcm.X86.Pclmul.pows)
      (.seq (.loop (.block Impl.Gcm.X86.Pclmul.body8) .ae) (.block Impl.Gcm.X86.Pclmul.after8)))) s
      fun s' => ∃ s₁ i, Base s₀ s₁ ∧ GPre s₁ ∧ Inv s₁ i s' := by
  refine WP.ite (decide (nBlk s₀ < 8)) (by simp only [X86.eval, c]) ?_ ?_
  · intro _
    exact WP.block_nil ⟨s₀, 0, Base.refl s₀, hp, hi⟩
  · intro h
    have hn : 8 ≤ nBlk s₀ := by have := of_decide_eq_false h; omega_using [this]
    refine WP.seq (WP.mono (pows_ok hp hi) fun s₁ k₁ => ?_)
    refine WP.seq (WP.mono (blocks8_ok hp k₁ hn) fun s₂ ⟨i, k₂, y₂, p₂⟩ => ?_)
    exact after8_ok hp k₂ y₂ p₂

theorem gh_correct (s₀ : State) (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.Pclmul.ghash s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  unfold Impl.Gcm.X86.Pclmul.ghash
  refine WP.seq (WP.mono (prologue_ok s₀ hp) fun s ⟨hi, c⟩ => ?_)
  refine WP.seq (WP.mono (groups_ok hp hi c) fun s₂ ⟨s₁, i, hb, hp₁, inv⟩ => ?_)
  refine WP.seq (WP.mono (test_ok s₂) fun s₃ ⟨z, ef, regs, xs⟩ => ?_)
  have inv₃ : Inv s₁ i s₃ := ⟨inv.env.trans ef, inv.le, by rw [regs]; exact inv.count,
    by rw [regs]; exact inv.data, by rw [regs]; exact inv.out, by rw [xs]; exact inv.rev,
    by rw [xs]; exact inv.poly, by rw [xs]; exact inv.hash, by rw [xs]; exact inv.acc⟩
  have bound : nBlk s₁ < 2 ^ 32 := (arg s₁ 3).isLt
  have z' : s₃.zf = some (decide (nBlk s₁ - i = 0)) := by
    rw [z, inv.count, Wp.ofNat_beq_zero (by omega_using [bound])]
  have loop : WP isa (.ite .e (.block []) (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne))
      s₃ (Inv s₁ (nBlk s₁)) := by
    refine WP.ite (decide (nBlk s₁ - i = 0)) (by simp only [X86.eval, z']) ?_ ?_
    · intro h
      have hle := inv.le
      obtain rfl : i = nBlk s₁ := by have := of_decide_eq_true h; omega_using [this, hle]
      exact WP.block_nil inv₃
    · intro h
      exact blocks_ok hp₁ inv₃ (by have := of_decide_eq_false h; omega_using [this])
  exact WP.seq (WP.mono loop fun s₄ inv₄ =>
    WP.mono (epilogue_ok hp₁ inv₄) fun s' hq => hb.finish hp hq)

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.Pclmul.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashX86.post s s' := gh_correct s (GPre.of hs)

end VG.Proof.Gcm.X86.Pclmul
