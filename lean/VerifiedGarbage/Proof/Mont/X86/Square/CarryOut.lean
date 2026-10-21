module

public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Square.OutStore
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
import VerifiedGarbage.Proof.Mont.X86.Square.CarryIn
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

def carryOut : List Instr := [.xop (.bin .movdqa .xmm3 .xmm0), .xop (.shift .psrlq .xmm3 32),
  .xop (.bin .paddq .xmm3 .xmm1)]

def carryOutState (s : State) : State :=
  let t1 := (XOp.bin .movdqa .xmm3 .xmm0).exec s
  let t2 := (XOp.shift .psrlq .xmm3 32).exec t1
  (XOp.bin .paddq .xmm3 .xmm1).exec t2

theorem run_carryOut (s : State) : runBlock isa carryOut s = some (carryOutState s) := by rfl

theorem carryOut_values {s : State} {l h : Nat}
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h)) (hl : l<2^64) :
    (carryOutState s).xmm .xmm3 = packed (BitVec.ofNat 64 (l/2^32+h)) ∧
    (carryOutState s).xmm .xmm7 = s.xmm .xmm7 := by
  have shift (a : BitVec 64) : XShiftOp.eval .psrlq (packed a) (32 : BitVec 8) = packed (a >>> 32) :=
    packed_shr a (by decide)
  simp only [carryOutState, XOp.exec]
  simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa, low, high,
    shift, shr32 hl, packed_add, BitVec.ofNat_add, and_self]

theorem carryOut_scalar (s : State) :
    (carryOutState s).gpr = s.gpr ∧ (carryOutState s).mem = s.mem ∧
    (carryOutState s).rd = s.rd ∧ (carryOutState s).wr = s.wr := by
  simp only [carryOutState, XOp.exec, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

end VG.Proof.Mont.X86.Square
