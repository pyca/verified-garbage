module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.ColumnMath
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Reduction
public import VerifiedGarbage.Proof.Mont.X86.Square.CarryOut
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EndCtl
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.PreparedSquare
open VG.Proof.Mont.X86.Square
open VG.Impl.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

def clear : List Instr := [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)]
def clearState (s : State) : State := (s.setXmm .xmm0 0).setXmm .xmm1 0

theorem run_clear (s : State) : runBlock isa clear s = some (clearState s) := by
  simp only [clear, runBlock_cons, exec, XOp.exec, XBinOp.eval, BitVec.xor_self, runStep_some, runBlock_nil]
  rfl

theorem clear_values (s : State) :
    (clearState s).xmm .xmm0 = packed 0 ∧ (clearState s).xmm .xmm1 = packed 0 ∧
    (clearState s).xmm .xmm3 = s.xmm .xmm3 ∧ (clearState s).xmm .xmm7 = s.xmm .xmm7 := by
  simp only [clearState]
  simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne]
  exact ⟨rfl, rfl, trivial, trivial⟩

theorem clear_scalar (s : State) :
    (clearState s).gpr=s.gpr ∧ (clearState s).mem=s.mem ∧
    (clearState s).rd=s.rd ∧ (clearState s).wr=s.wr := by
  simp only [clearState, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

theorem reduction_wp (s : State) (Q : State → Prop) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.reduction s Q ↔ WP isa reductionCode s Q := by
  simp [VG.Impl.Mont.X86.PreparedSquare.reduction, VG.Impl.Mont.X86.PreparedSquare.seqs, reductionCode, redStage, lower, redPtr, redEnd,
    snapshot, widthTest, digitFull, digitStore, prodByB, outStore, ptr, argM, argInv, cacheArg, ↓reduceIte,
    WP.seq_iff (M := isa), List.cons_append, List.nil_append]

def columnCode : Prog isa := .seq (.block clear) (.seq VG.Impl.Mont.X86.PreparedSquare.cross (.seq (.block VG.Impl.Mont.X86.Rt.Square.carryIn)
  (.seq reductionCode (.block (carryOut ++ endCtl)))))

theorem column_wp (s : State) (Q : State → Prop) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.column s Q ↔ WP isa columnCode s Q := by
  simp only [VG.Impl.Mont.X86.PreparedSquare.column, VG.Impl.Mont.X86.PreparedSquare.seqs, columnCode, clear, carryOut, endCtl,
    WP.seq_iff (M := isa), reduction_wp, List.cons_append, List.nil_append]

end VG.Proof.Mont.X86.PreparedSquare
