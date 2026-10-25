module

public import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # Reducing a scan without a temporary memory round trip -/

@[expose] public section

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem reduceOr_ok (s : State) :
    ∃ s', runBlock isa Sse2.reduceOr s = some s' ∧
      s'.xmm .xmm1 = reduceValue (s.xmm .xmm1) ∧
      KeepX [] [.xmm1, .xmm3] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, not_false_eq_true, Sse2.reduceOr, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  constructor
  · simp only [xmm_setXmm_self,
      XBinOp.eval, XShiftOp.eval]
    rfl
  · constructor
    · constructor
      · intro r _; simp only [gpr_setXmm]
      · simp only [mem_setXmm]
      · simp only [rd_setXmm]
      · simp only [wr_setXmm]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2]

theorem finishTail_ok (s : State) :
    ∃ s', runBlock isa [.movqR .rax .xmm1, .alu .and .rax (.imm 65535)] s = some s' ∧
      s'.gpr .rax = (word (s.xmm .xmm1) 0).setWidth 64 ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg_self]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    rw [show (65535 : BitVec 32).signExtend 64 = (65535 : BitVec 64) by decide, maskWord]
    congr 1
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [word, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', decide_eq_true hi, decide_eq_true (show i < 64 by omega), Bool.true_and, Nat.mul_zero, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Sse2
