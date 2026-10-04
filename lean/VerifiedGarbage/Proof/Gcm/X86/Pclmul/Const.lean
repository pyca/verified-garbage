import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Arith
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

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

theorem acc_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.acc) s fun s' =>
      prod s' = (prod s).acc (s.xmm .xmm2) (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm7] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.acc]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [prod, Prod.acc, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
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
    WP isa (.block (Impl.Gcm.X86.Pclmul.zero ++ Impl.Gcm.X86.Pclmul.acc ++
      Impl.Gcm.X86.Pclmul.reduce)) s fun s' =>
      φ (s'.xmm .xmm2) = x * φ (s.xmm .xmm2) * φ (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok s₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by
    rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1]
  refine WP.mono (reduce_ok s₂ e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, φ_reduce, p₂, p₁, Prod.val_acc, Prod.val_zero, zero_add,
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
  catWord (catWord (catWord ((0 : BitVec 96) ++ c.extractLsb' 96 32)
    (c.extractLsb' 64 32)) (c.extractLsb' 32 32)) (c.extractLsb' 0 32)

theorem assembled_eq (c : BitVec 128) : assembled c = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [assembled, catWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
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
