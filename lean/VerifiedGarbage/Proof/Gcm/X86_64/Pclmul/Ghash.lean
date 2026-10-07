import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.HInvBits
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Blocks`.
section

section

/-!
# GHASH with PCLMULQDQ: the arithmetic

What the instructions of `Impl.Gcm.X86_64.Pclmul` compute, in the ring `Q` of
`Proof/Gcm/Poly.lean`:

* `pclmulqdq` multiplies polynomials (`gp_clmul`), so the four of `acc`
  compute `x · a · b` as a 256-bit value (`Prod.val_acc`);
* `reduce` maps a 256-bit value to a block of the same class
  (`φ_reduce`);
* `hInv` computes `H · x⁻¹` (`x_φ_hInv`).
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open Polynomial
open VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (poly xInv)

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
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

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

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

theorem val_zero : zero.val = 0 := by simp only [val, zero, BitVec.ofNat_eq_ofNat, φ_zero', mul_zero, add_zero]

theorem val_acc (p : Prod) (a b : BitVec 128) : (p.acc a b).val = p.val + x * φ a * φ b := by
  simp only [acc, val, φ_xor]
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x01 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x01 : BitVec 8).getLsbD 4 = false from rfl, show (0x10 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x10 : BitVec 8).getLsbD 4 = true from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    φ_clmul, φ_q a, φ_q b]
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
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6)) with
        rfl | rfl | rfl | ⟨h0, h1, h6⟩
      · decide
      · decide
      · decide
      · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : (qword poly 1).getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
      rw [e]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega, show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega]
  simp only [ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem shufDwords_4e (a : BitVec 128) : shufDwords a 0x4e = qword a 0 ++ qword a 1 := by
  rw [show shufDwords a 0x4e = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_ofDwords, getLsbD_dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega)

theorem φ_fold (v : BitVec 128) : φ (fold v) = x ^ 64 * φ v := by
  have e1 : φ (shufDwords v 0x4e) = ψ (qword v 0) + x ^ 64 * ψ (qword v 1) := by
    rw [shufDwords_4e, φ, gp_append]; simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, ψ]
  have e2 : pclmul v poly 0x10 = clmul (qword v 0) (qword poly 1) := rfl
  rw [fold, φ_xor, e1, e2, φ_clmul, ψ_c, φ_q v]
  linear_combination (-ψ (qword v 0)) * x128

theorem φ_reduce (p : Prod) : φ (reduce p) = p.val := by
  simp only [reduce, φ_xor, φ_fold, φ_shr64, φ_shl64, Prod.val, φ_q p.mid]
  ring

theorem φ_reduceB (p : Prod) : φ (reduceB p) = p.val := by
  simp only [reduceB, φ_xor, φ_fold, Prod.val]
  ring

/-! ## `H · x⁻¹` (its bits: `Pclmul/HInvBits.lean`) -/

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
    · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, h7, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv.getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega, show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega, show d ≠ 127 by omega]

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

end VG.Proof.Gcm.X86_64.Pclmul

end

/-!
# GHASH with PCLMULQDQ: the instruction groups

What each group of instructions of `Impl.Gcm.X86_64.Pclmul` does to the state,
each proved by one symbolic execution for any registers it is used with.
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly xInv)

/-- `d ← mul(a, b)`, a block of class `x · a · b`. -/
theorem mul_ok (d a b : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (ha11 : a ≠ .xmm11) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11)
    (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11)
    (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul d a b)) s fun s' =>
      φ (s'.xmm d) = x * φ (s.xmm a) * φ (s.xmm b) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' := by
  rw [Impl.Gcm.X86_64.Pclmul.mul, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok a b s₁ ha8 ha9 ha10 ha11 hb8 hb9 hb10 hb11) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1]
  refine WP.mono (reduce_ok d s₂ hd8 hd9 hd10 hd11 e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, φ_reduce, p₂, p₁, Prod.val_acc, Prod.val_zero, zero_add,
      o₁.xmm a (by simp only [List.mem_cons, ha8, ha9, ha10, List.not_mem_nil, or_self, not_false_eq_true]), o₁.xmm b (by simp only [List.mem_cons, hb8, hb9, hb10, List.not_mem_nil, or_self, not_false_eq_true])]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

/-- `H' = H · x⁻¹` into `xmm3`, from `H` in `xmm7`. -/
theorem hInv_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Pclmul.hInv) s fun s' =>
      x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      Only [.xmm3, .xmm11, .xmm12, .xmm13, .xmm14] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.hInv, Impl.Gcm.X86_64.Pclmul.const, List.cons_append,
    List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.setReg, ite_true, ite_false, movq_const, eval_movdqa, eval_pxor,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp only [hr, ↓reduceIte], rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [show XBinOp.eval .por (XShiftOp.eval .psllq (s.xmm .xmm7) 1)
        (XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) =
        XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
          XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8 from rfl,
      shl1, mask_eq, x_φ_hInv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `H'²`, then `H'³` and `H'⁴` from it, into `xmm4`–`xmm6`, for any hash
subkey `H` whose `H'` is in `xmm3`. -/
theorem pows_ok {H : Spec.Gcm.Block} (s : State) (h1 : s.xmm .xmm1 = poly) (hH : x * φ (s.xmm .xmm3) = φ H) :
    WP isa (.block Impl.Gcm.X86_64.Pclmul.pows) s fun s' =>
      x * φ (s'.xmm .xmm4) = φ H ^ 2 ∧ x * φ (s'.xmm .xmm5) = φ H ^ 3 ∧
      x * φ (s'.xmm .xmm6) = φ H ^ 4 ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  simp only [Impl.Gcm.X86_64.Pclmul.pows, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm4 .xmm3 .xmm3 s (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1)
    fun s₁ ⟨m₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm5 .xmm4 .xmm3 s₁ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁.xmm _ (by decide), h1])) fun s₂ ⟨m₂, o₂⟩ => ?_
  refine WP.mono (mul_ok .xmm6 .xmm4 .xmm4 s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1])) fun s₃ ⟨m₃, o₃⟩ => ?_
  have H2 : x * φ (s₁.xmm .xmm4) = φ H ^ 2 := by
    rw [m₁, show ∀ a : Q, x * (x * a * a) = (x * a) * (x * a) from fun a => by ring, hH]; ring
  have H3 : x * φ (s₂.xmm .xmm5) = φ H ^ 3 := by
    rw [m₂, o₁.xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, H2, hH]; ring
  have H4 : x * φ (s₃.xmm .xmm6) = φ H ^ 4 := by
    rw [m₃, o₂.xmm .xmm4 (by decide),
      show ∀ a : Q, x * (x * a * a) = (x * a) * (x * a) from fun a => by ring, H2]; ring
  refine ⟨by rw [(o₂.trans o₃).xmm _ (by decide)]; exact H2, by rw [o₃.xmm _ (by decide)]; exact H3, H4,
    (o₁.trans (o₂.trans o₃)).weaken fun r hr => ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h) <;> simp [h]

end VG.Proof.Gcm.X86_64.Pclmul

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash`.
section

/-!
# GHASH with PCLMULQDQ: the whole function

`ghash_verified` proves `Impl.Gcm.X86_64.Pclmul.ghash` against `ghashX86_64`.

The registers `xmm3`–`xmm6` hold `Tₖ` with `x · Tₖ = Hᵏ` (`k = 1 … 4`), so
that `mul(a, Tₖ) = a · Hᵏ`, and `xmm2` holds `Y` after `i` blocks, as a
block; the memory is not written until the epilogue stores `Y`.
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open Spec.Gcm

open VG.X86_64 in
/-- X86-64 contract for `vg_ghash_pclmul(h: *const [u8; 16], y: *mut [u8; 16],
data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`: replaces the block
`Y` at `y` with `GHASH_H` continued from `Y` over the `n` blocks at `data`,
where `H` is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes). `y` and `scratch` may not
overlap each other, the other buffers, or the return address on the stack.
The pointers and `n` are public; `H`, `Y` and the data are secret. -/
def ghashX86_64 : Contract X86_64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .rdi, 16⟩
    let y : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ ret.Disjoint y ∧ ret.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .rsi) =
      ghashFrom (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
        (blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

end VG.Proof.Gcm.X86_64.Pclmul

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly prologue body4 body1 epilogue ghashTail ghash)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Four blocks and one block, in `Q` -/

theorem step4 (H Y X₁ X₂ X₃ X₄ T₁ T₂ T₃ T₄ : Block) (h₁ : x * φ T₁ = φ H)
    (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) :
    reduce ((((Prod.zero.acc (Y ^^^ X₁) T₄).acc X₂ T₃).acc X₃ T₂).acc X₄ T₁) =
      mul (mul (mul (mul (Y ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H := by
  apply φ_inj
  simp only [φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₄ + φ X₂ * h₃ + φ X₃ * h₂ + φ X₄ * h₁

theorem step1 (H Y X₁ T₁ : Block) (h₁ : x * φ T₁ = φ H) :
    reduce (Prod.zero.acc (Y ^^^ X₁) T₁) = mul (Y ^^^ X₁) H := by
  apply φ_inj
  simp only [φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₁

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp only [BitVec.ofInt_natCast]

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem add_zero' (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p := by
  rw [ofInt_natCast]; exact BitVec.add_zero p

theorem addr_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (b : Int) = p + BitVec.ofNat 64 (a + b) := by
  rw [ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .rdi
abbrev yp : Addr := s₀.gpr .rsi
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : ghashX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, zero_add, Nat.one_le_ofNat]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h : InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨hR s₀, by simp only [h.rd, List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀, true_or], by rw [ofInt_natCast]; exact contains_offset (by decide) (by decide)⟩

theorem in_y : InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨yR s₀, by simp only [h.wr, List.mem_append, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_self, or_false, or_true], by rw [ofInt_natCast]; exact contains_offset (by decide) (by decide)⟩

theorem out_y : InRegions s₀.wr (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨yR s₀, by simp only [h.wr, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_self, or_false], by rw [ofInt_natCast]; exact contains_offset (by decide) (by decide)⟩

/-- Block `i + j` is in the data. -/
theorem in_blk {i j : Nat} (hij : i + j < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp only [h.rd, List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, true_or, or_true], ?_⟩
  rw [addr_add, ← Nat.mul_add]
  exact contains_offset (by omega) (by omega)

end Pre

/-! ## The loop invariant -/

/-- What holds after `i` blocks: `H'²`–`H'⁴` only with four blocks or more,
which the prologue computes only then (`withPows_ok`). -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  t1 : x * φ (s.xmm .xmm3) = φ (H₀ s₀)
  t2 : 4 ≤ nb s₀ → x * φ (s.xmm .xmm4) = φ (H₀ s₀) ^ 2
  t3 : 4 ≤ nb s₀ → x * φ (s.xmm .xmm5) = φ (H₀ s₀) ^ 3
  t4 : 4 ≤ nb s₀ → x * φ (s.xmm .xmm6) = φ (H₀ s₀) ^ 4
  y : s.xmm .xmm2 = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s.gpr r = s₀.gpr r
  rdx : s.gpr .rdx = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loads of a block body: block `i + j`, into `xmm7`. -/
theorem load_blk {s₀ : State} (hp : Pre s₀) {i j : Nat} (hij : i + j < nb s₀) {s : State}
    (h0 : s.xmm .xmm0 = revMask) (hrdx : s.gpr .rdx = blkAddr s₀ i) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.load j)) s fun s' =>
      s'.xmm .xmm7 = blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (i + j))) ∧ Only [.xmm7] s s' := by
  refine WP.mono (ldrev_ok .xmm7 .rdx (16 * j) s (by decide) h0
    (by rw [hrd, hwr, hrdx]; exact hp.in_blk hij)) fun s' ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hrdx, hm, addr_add, Nat.mul_add]

/-- `rdx + b`, for `rdx` at an offset `a` into the data. -/
theorem add_ofNat_ofNat (p : Addr) {a b c : Nat} (h : a + b = c) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 c := Offset.add_add_eq p h

/-- The end of a body: `add rdx, 16 k`, `sub rcx, k`, and for the four-block
body `cmp rcx, 4`. -/
theorem tail4_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 64), .alu .sub .rcx (.imm 4), .alu .cmp .rcx (.imm 4)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 64 ∧ s'.gpr .rcx = s.gpr .rcx - 4 ∧
        s'.cf = some (decide ((s.gpr .rcx - 4).toNat < 4)) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e64, e4,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], trivial⟩

theorem tail1_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e16, e1,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], trivial⟩

/-! ## The bodies -/

theorem body4_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + 4 ≤ nb s₀) {s : State}
    (hI : Inv s₀ i s) :
    WP isa (.block body4) s fun s' =>
      Inv s₀ (i + 4) s' ∧ s'.cf = some (decide (nb s₀ - (i + 4) < 4)) := by
  have hn := hp.nb_lt
  simp only [body4, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 0) (by omega) (by rw [o₁.xmm _ (by decide), hI.x0])
    (by rw [o₁.gpr _ (by decide), hI.rdx]) (o₁.mem.trans hI.mem) (o₁.rd.trans hI.rd)
    (o₁.wr.trans hI.wr)) fun s₂ ⟨l₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm6 s₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨p₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 1) (by omega) (by rw [o₁₄.xmm _ (by decide), hI.x0])
    (by rw [o₁₄.gpr _ (by decide), hI.rdx]) (o₁₄.mem.trans hI.mem) (o₁₄.rd.trans hI.rd)
    (o₁₄.wr.trans hI.wr)) fun s₅ ⟨l₅, o₅⟩ => ?_
  have o₁₅ := o₁₄.trans o₅
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm5 s₅ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₆ ⟨p₆, o₆⟩ => ?_
  have o₁₆ := o₁₅.trans o₆
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 2) (by omega) (by rw [o₁₆.xmm _ (by decide), hI.x0])
    (by rw [o₁₆.gpr _ (by decide), hI.rdx]) (o₁₆.mem.trans hI.mem) (o₁₆.rd.trans hI.rd)
    (o₁₆.wr.trans hI.wr)) fun s₇ ⟨l₇, o₇⟩ => ?_
  have o₁₇ := o₁₆.trans o₇
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm4 s₇ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₈ ⟨p₈, o₈⟩ => ?_
  have o₁₈ := o₁₇.trans o₈
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 3) (by omega) (by rw [o₁₈.xmm _ (by decide), hI.x0])
    (by rw [o₁₈.gpr _ (by decide), hI.rdx]) (o₁₈.mem.trans hI.mem) (o₁₈.rd.trans hI.rd)
    (o₁₈.wr.trans hI.wr)) fun s₉ ⟨l₉, o₉⟩ => ?_
  have o₁₉ := o₁₈.trans o₉
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₉ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₁₀ ⟨p₁₀, o₁₀⟩ => ?_
  have o₁₁₀ := o₁₉.trans o₁₀
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₁₀ (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁₁₀.xmm _ (by decide), hI.x1])) fun s₁₁ ⟨p₁₁, o₁₁⟩ => ?_
  have o₁₁₁ := o₁₁₀.trans o₁₁
  refine WP.mono (tail4_ok s₁₁) fun s' ⟨frdx, frcx, fcf, fg, fx, fm, frd, fwr⟩ => ?_
  have hrdx : s₁₁.gpr .rdx = blkAddr s₀ i := by rw [o₁₁₁.gpr _ (by decide), hI.rdx]
  have hrcx : s₁₁.gpr .rcx - 4 = BitVec.ofNat 64 (nb s₀ - (i + 4)) := by
    rw [o₁₁₁.gpr _ (by decide), hI.rcx]
    exact ofNat_sub_ofNat (k := 4) (by omega) (by have := (s₀.gpr .rcx).isLt; omega)
  have kx : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      s'.xmm r = s.xmm r := fun r h2 h7 h8 h9 h10 h11 => by
    rw [fx, o₁₁₁.xmm r (by simp only [List.cons_append, List.nil_append, List.mem_cons, h8, h9, h10, h7, h11, h2, List.not_mem_nil, or_self, not_false_eq_true])]
  refine ⟨⟨by omega, by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x0], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t1], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t2 h], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t3 h], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t4 h], ?_, fun r ha hd hc => by rw [fg r hd hc, o₁₁₁.gpr r ha, hI.gpr r ha hd hc],
      by rw [frdx, hrdx]; exact add_ofNat_ofNat (b := 64) _ (by omega), by rw [frcx, hrcx],
      by rw [fm, o₁₁₁.mem, hI.mem], by rw [frd, o₁₁₁.rd, hI.rd], by rw [fwr, o₁₁₁.wr, hI.wr]⟩, ?_⟩
  · -- The new `Y`.
    rw [fx, p₁₁, p₁₀, o₉.prod (by decide) (by decide) (by decide), p₈,
      o₇.prod (by decide) (by decide) (by decide), p₆, o₅.prod (by decide) (by decide) (by decide), p₄,
      o₃.prod (by decide) (by decide) (by decide), o₂.prod (by decide) (by decide) (by decide), p₁,
      l₉, l₇, l₅, l₃, l₂, o₁₉.xmm .xmm3 (by decide), o₁₇.xmm .xmm4 (by decide),
      o₁₅.xmm .xmm5 (by decide), o₁₃.xmm .xmm6 (by decide), o₁₂.xmm .xmm2 (by decide), hI.y,
      show i + 4 = i + 3 + 1 from rfl, ghashFrom_blocksAt_succ, show i + 3 = i + 2 + 1 from rfl,
      ghashFrom_blocksAt_succ, show i + 2 = i + 1 + 1 from rfl, ghashFrom_blocksAt_succ,
      ghashFrom_blocksAt_succ, Nat.add_zero]
    have h4 : 4 ≤ nb s₀ := by omega
    exact step4 _ _ _ _ _ _ _ _ _ _ hI.t1 (hI.t2 h4) (hI.t3 h4) (hI.t4 h4)
  · rw [fcf, hrcx, toNat_ofNat_lt (by omega)]

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

theorem body1_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hI : Inv s₀ i s) :
    WP isa (.block body1) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nb s₀ - (i + 1) = 0)) := by
  have hn := hp.nb_lt
  simp only [body1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 0) (by omega) (by rw [o₁.xmm _ (by decide), hI.x0])
    (by rw [o₁.gpr _ (by decide), hI.rdx]) (o₁.mem.trans hI.mem) (o₁.rd.trans hI.rd)
    (o₁.wr.trans hI.wr)) fun s₂ ⟨l₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨p₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₄ (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁₄.xmm _ (by decide), hI.x1])) fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₁₅ := o₁₄.trans o₅
  refine WP.mono (tail1_ok s₅) fun s' ⟨frdx, frcx, fzf, fg, fx, fm, frd, fwr⟩ => ?_
  have hrdx : s₅.gpr .rdx = blkAddr s₀ i := by rw [o₁₅.gpr _ (by decide), hI.rdx]
  have hrcx : s₅.gpr .rcx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [o₁₅.gpr _ (by decide), hI.rcx]
    exact ofNat_sub_ofNat (k := 1) (by omega) (by have := (s₀.gpr .rcx).isLt; omega)
  have kx : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      s'.xmm r = s.xmm r := fun r h2 h7 h8 h9 h10 h11 => by
    rw [fx, o₁₅.xmm r (by simp only [List.cons_append, List.nil_append, List.mem_cons, h8, h9, h10, h7, h11, h2, List.not_mem_nil, or_self, not_false_eq_true])]
  refine ⟨⟨by omega, by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x0], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t1], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t2 h], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t3 h], fun h => by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t4 h], ?_, fun r ha hd hc => by rw [fg r hd hc, o₁₅.gpr r ha, hI.gpr r ha hd hc],
      by rw [frdx, hrdx]; exact add_ofNat_ofNat (b := 16) _ (by omega), by rw [frcx, hrcx],
      by rw [fm, o₁₅.mem, hI.mem], by rw [frd, o₁₅.rd, hI.rd], by rw [fwr, o₁₅.wr, hI.wr]⟩, ?_⟩
  · rw [fx, p₅, p₄, o₃.prod (by decide) (by decide) (by decide), o₂.prod (by decide) (by decide)
      (by decide), p₁, l₃, l₂, o₁₃.xmm .xmm3 (by decide), o₁₂.xmm .xmm2 (by decide), hI.y,
      ghashFrom_blocksAt_succ, Nat.add_zero]
    exact step1 _ _ _ _ hI.t1
  · rw [fzf, hrcx, beq_ofNat_zero (by omega)]

/-! ## The prologue and the epilogue -/

/-- `Y` loaded into `xmm2`, and `cmp rcx, 4`. -/
theorem loadY_ok (s : State) (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm2 (at_ .rsi 0), .xop (.bin .pshufb .xmm2 .xmm0),
        .alu .cmp .rcx (.imm 4)]) s fun s' =>
      s'.xmm .xmm2 = blockAt s.mem (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) ∧
      s'.cf = some (decide ((s.gpr .rcx).toNat < 4)) ∧ Only [.xmm2] s s' := by
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.load128, ea_at, hin,
    ite_true, ite_false, h0, e4, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

/-- What holds after the prologue: `Inv s₀ 0` but for `H'²`–`H'⁴`. -/
structure Base (s₀ s : State) : Prop where
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  t1 : x * φ (s.xmm .xmm3) = φ (H₀ s₀)
  y : s.xmm .xmm2 = Y₀ s₀
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `Base`, with `H'²`–`H'⁴` if there are four blocks or more, is the
invariant before any block. -/
theorem Base.inv {s₀ s : State} (hB : Base s₀ s)
    (hP : 4 ≤ nb s₀ → x * φ (s.xmm .xmm4) = φ (H₀ s₀) ^ 2 ∧ x * φ (s.xmm .xmm5) = φ (H₀ s₀) ^ 3 ∧
      x * φ (s.xmm .xmm6) = φ (H₀ s₀) ^ 4) :
    Inv s₀ 0 s :=
  ⟨Nat.zero_le _, hB.x0, hB.x1, hB.t1, fun h => (hP h).1, fun h => (hP h).2.1, fun h => (hP h).2.2,
    by rw [hB.y, ghashFrom_blocksAt_zero], fun r ha _ _ => hB.gpr r ha,
    by rw [hB.gpr _ (by decide)]; simp only [blkAddr, mul_zero, BitVec.add_zero],
    by rw [hB.gpr _ (by decide)]; simp only [nb, tsub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    hB.mem, hB.rd, hB.wr⟩

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s' => Base s₀ s' ∧ s'.cf = some (decide (nb s₀ < 4)) := by
  simp only [prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 0 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hp.in_h)) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  refine WP.mono (loadY_ok s₄ (by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide),
      c₁, rev_eq])
    (by rw [o₁₄.rd, o₁₄.wr, o₁₄.gpr _ (by decide)]; exact hp.in_y)) fun s' ⟨ly, fcf, oy⟩ => ?_
  have O := o₁₄.trans oy
  refine ⟨⟨by rw [(o₂.trans (o₃.trans (o₄.trans oy))).xmm _ (by decide), c₁, rev_eq],
    by rw [(o₃.trans (o₄.trans oy)).xmm _ (by decide), c₂],
    by rw [oy.xmm _ (by decide), t₄, l₃, add_zero', o₁₂.mem, o₁₂.gpr _ (by decide)],
    by rw [ly, o₁₄.mem, o₁₄.gpr _ (by decide), add_zero'],
    fun r ha => O.gpr r ha, O.mem, O.rd, O.wr⟩, by rw [fcf, o₁₄.gpr _ (by decide)]⟩

/-- After the prologue: `H'²`–`H'⁴` unless there are fewer than four blocks,
and `rest`. -/
theorem withPows_ok {s₀ s : State} (hB : Base s₀ s) (hcf : s.cf = some (decide (nb s₀ < 4)))
    {rest : Prog isa} {Q : State → Prop} (hlt : Inv s₀ 0 s → nb s₀ < 4 → Q s)
    (hrest : ∀ s', Inv s₀ 0 s' → 4 ≤ nb s₀ → WP isa rest s' Q) :
    WP isa (Impl.Gcm.X86_64.Pclmul.withPows rest) s Q := by
  refine WP.ite (decide (nb s₀ < 4)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · have h' : nb s₀ < 4 := of_decide_eq_true h
    exact WP.block_nil (hlt (hB.inv fun h4 => absurd h4 (by omega)) h')
  · have h' : 4 ≤ nb s₀ := Nat.le_of_not_lt (of_decide_eq_false h)
    refine WP.seq (WP.mono (pows_ok s hB.x1 hB.t1) fun s' ⟨H2, H3, H4, o⟩ => hrest s' ?_ h')
    exact Base.inv ⟨by rw [o.xmm _ (by decide), hB.x0], by rw [o.xmm _ (by decide), hB.x1],
      by rw [o.xmm _ (by decide)]; exact hB.t1, by rw [o.xmm _ (by decide), hB.y],
      fun r ha => by rw [o.gpr r ha, hB.gpr r ha], by rw [o.mem, hB.mem], by rw [o.rd, hB.rd],
      by rw [o.wr, hB.wr]⟩ fun _ => ⟨H2, H3, H4⟩

/-- `cmp rcx, c`, after `i` blocks. -/
theorem cmp_ok {s₀ : State} (hp : Pre s₀) {i : Nat} {s : State} (hI : Inv s₀ i s) (c : Nat) (hc : c < 2 ^ 31)
    (ec : BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      Inv s₀ i s' ∧ s'.cf = some (decide (nb s₀ - i < c)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, ec, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with }, ?_⟩
  simp only [toNat_ofNat_lt (show nb s₀ - i < 2 ^ 64 by omega), toNat_ofNat_lt (show c < 2 ^ 64 by omega)]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [hI.wr, hI.gpr .rsi (by decide) (by decide) (by decide)]; exact hp.out_y
  have h0 := hI.x0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [epilogue, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hout, ite_true, h0,
    Option.some.injEq, exists_eq_left']
  rw [add_zero', hI.gpr .rsi (by decide) (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [Mem.readW_writeW_sep (hp.ret_y.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), hI.mem]
  · show blockAt _ (yp s₀) = _
    rw [blockAt_store, hI.y]

theorem test_ok {s₀ : State} (hp : Pre s₀) {i : Nat} {s : State} (hI : Inv s₀ i s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      Inv s₀ i s' ∧ s'.zf = some (decide (nb s₀ - i = 0)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with }, by rw [beq_ofNat_zero (by omega)]⟩

/-! ## The whole function -/

/-- The blocks left after `i₀`, four and then one at a time, and `Y` stored:
what follows the prologue here, and the eight-block loop of
`vg_ghash_vpclmul`. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {i₀ : Nat} {s₁ : State} (hI₁ : Inv s₀ i₀ s₁)
    (hcf : s₁.cf = some (decide (nb s₀ - i₀ < 4))) :
    WP isa ghashTail s₁ fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 4 ∧ Inv s₀ i s) ?_ fun s₂ ⟨i, hi, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ - i₀ < 4)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨i₀, by simpa using h, hI₁⟩
    · let Inv4 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 4 ≤ nb s₀ ∧ Inv s₀ i s
      have hstep : ∀ m s, Inv4 m s → WP isa (.block body4) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ i, nb s₀ - i < 4 ∧ Inv s₀ i s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, Inv4 m' s')) := by
        rintro m s ⟨i, rfl, hi, hI⟩
        refine WP.mono (body4_ok hp hi hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nb s₀ - (i + 4) < 4
        · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true], i + 4, hlt, hI'⟩
        · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false], nb s₀ - (i + 4), by omega, i + 4, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) Inv4 hstep (nb s₀ - i₀) s₁ ⟨i₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀)) ?_ fun s₄ hI₄ => epilogue_ok hp hI₄)
  refine WP.ite (decide (nb s₀ - i = 0)) (by simp only [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : i = nb s₀ := by have := hI₃.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block body1) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body1_ok hp hi hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by simp only [eval, hzf', hlast, decide_true, Option.map_some, Bool.not_true], this ▸ hI'⟩
      · exact .inr ⟨by simp only [eval, hzf', hlast, decide_false, Option.map_some, Bool.not_false], nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩
    have hlt : i < nb s₀ := by have := hI₃.le; simp only [decide_eq_false_iff_not] at h; omega
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s₃ ⟨i, rfl, hlt, hI₃⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' :=
  WP.seq (WP.mono (prologue_ok hp) fun _ ⟨hB, hcf⟩ =>
    WP.seq (WP.mono (withPows_ok (Q := Inv s₀ 0) hB hcf (fun hI _ => hI) fun _ hI _ => WP.block_nil hI)
      fun _ hI => WP.seq (WP.mono (cmp_ok hp hI 4 (by decide) (by decide)) fun _ ⟨hI', hcf'⟩ =>
        tail_ok hp hI' hcf')))

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_correct (s : State) (hs : ghashX86_64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86_64.Pclmul.ghash s t s' ∧ abiPreserved s s' ∧ ghashX86_64.post s s'
      := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem ghash_ct : ConstantTime isa ghashX86_64.pre ghashX86_64.pub Impl.Gcm.X86_64.Pclmul.ghash :=
    by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ghash_verified :
    Verified X86_64.target Impl.Gcm.X86_64.Pclmul.ghash (Spec.Gcm.ghashContract X86_64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.X86_64.Pclmul.ghashX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Gcm.X86_64.Pclmul.satState] using
      Proof.Gcm.X86_64.Pclmul.satState)

end VG.Proof.Gcm.X86_64.Pclmul

end
