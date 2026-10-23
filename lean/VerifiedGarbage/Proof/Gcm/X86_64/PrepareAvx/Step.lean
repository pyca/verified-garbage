module

public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# Squares and products for `vg_aes_gcm_prepare16_pclmul_avx`, on SSE code

The SSE code that `PrepareAvx.sq` and `PrepareAvx.mulD` run on the lower
lanes: a square from its low and high products alone (`sq_val`: the middle
term of a square is zero in characteristic 2), and a product summed
straight into `xmm8`–`xmm10` and reduced the low half first (`reduceB`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.PrepareAvx

open VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod Only fold eval_pxor)
open VG.Impl.Gcm.X86_64.Pclmul (poly)

/-- The SSE code of `PrepareAvx.sq d a`. -/
def sqS (d a : XReg) : List Instr :=
  [.xop (.bin .movdqa .xmm8 a), .xop (.pclmulqdq .xmm8 a 0x00),
   .xop (.bin .movdqa .xmm10 a), .xop (.pclmulqdq .xmm10 a 0x11)] ++
  Impl.Gcm.X86_64.Pclmul.fold ++ Impl.Gcm.X86_64.Pclmul.fold ++
  [.xop (.bin .movdqa d .xmm10), .xop (.bin .pxor d .xmm8)]

/-- The SSE code of `PrepareAvx.mulD d a b`. -/
def mulDS (d a b : XReg) : List Instr :=
  [.xop (.bin .movdqa .xmm8 a), .xop (.pclmulqdq .xmm8 b 0x00),
   .xop (.bin .movdqa .xmm10 a), .xop (.pclmulqdq .xmm10 b 0x11),
   .xop (.bin .movdqa .xmm9 a), .xop (.pclmulqdq .xmm9 b 0x01),
   .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 b 0x10),
   .xop (.bin .pxor .xmm9 .xmm11)] ++
  Impl.Gcm.X86_64.Pclmul.fold ++
  [.xop (.bin .pxor .xmm9 .xmm8),
   .xop (.bin .movdqa .xmm11 .xmm9), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm9 .xmm9 0x4e), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa d .xmm10), .xop (.bin .pxor d .xmm9)]

/-- A square needs no middle term: `x · a²` from the low and high products. -/
theorem sq_val (a : BitVec 128) :
    φ (pclmul a a 0x11) + x ^ 128 * φ (pclmul a a 0x00) = x * φ a * φ a := by
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    Pclmul.φ_clmul, Pclmul.φ_q a]
  linear_combination (-(x ^ 65 * Pclmul.ψ (qword a 1) * Pclmul.ψ (qword a 0))) * two_Q

theorem zero_xor (v : BitVec 128) : 0 ^^^ v = v := BitVec.zero_xor

theorem fold_eq (v : BitVec 128) : shufDwords v 0x4e ^^^ pclmul v poly 0x10 = fold v := rfl

theorem sqS_ok (d a : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha10 : a ≠ .xmm10)
    (hd8 : d ≠ .xmm8) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (sqS d a)) s fun s' =>
      φ (s'.xmm d) = x * φ (s.xmm a) * φ (s.xmm a) ∧ Only [.xmm8, .xmm10, .xmm11, d] s s' := by
  apply WP.of_runBlock
  simp only [sqS, Impl.Gcm.X86_64.Pclmul.fold, List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, eval_movdqa, ha8, ha10, hd8, hd10, hd11, Ne.symm hd8, h1,
    Option.some.injEq, exists_eq_left', fold_eq]
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [φ_xor, Pclmul.φ_fold, Pclmul.φ_fold, ← sq_val]
    ring
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem mulDS_ok (d a b : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11)
    (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (mulDS d a b)) s fun s' =>
      φ (s'.xmm d) = x * φ (s.xmm a) * φ (s.xmm b) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' := by
  apply WP.of_runBlock
  simp only [mulDS, Impl.Gcm.X86_64.Pclmul.fold, List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, eval_movdqa, ha8, ha9, ha10, hb8, hb9, hb10, hb11,
    hd8, hd9, hd10, hd11, Ne.symm hd9, h1, Option.some.injEq, exists_eq_left', fold_eq]
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · have e := Pclmul.φ_reduceB (Prod.zero.acc (s.xmm a) (s.xmm b))
    rw [Pclmul.Prod.val_acc, Pclmul.Prod.val_zero, zero_add] at e
    rw [← e]
    simp only [Pclmul.reduceB, Prod.acc, Prod.zero, zero_xor]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Gcm.X86_64.PrepareAvx
