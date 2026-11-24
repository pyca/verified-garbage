module

public import VerifiedGarbage.Impl.Gcm.X86.Pclmul
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Gcm.X86.Rev
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-!
# GHASH with PCLMULQDQ: constants and byte-reversed blocks

`Impl.Gcm.X86.Pclmul.const`, and a load and byte reversal of a block, apart
from the proof of the function (`Ghash.lean`), which imports the algebra of
`Proof/Gcm/Poly.lean`: GCM-SIV uses them too.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86.Pclmul

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Gcm.X86.Pclmul (at_)

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
