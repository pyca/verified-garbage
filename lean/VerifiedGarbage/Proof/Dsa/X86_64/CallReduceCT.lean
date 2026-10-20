module

public import VerifiedGarbage.Proof.Dsa.X86_64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.Arguments2
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave

/-! # Constant time of the complete parent-to-child reduction call -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CallReducePublic extends ReduceFinishPublic where
  parentInverse : BitVec 64
  extent : pWorkspace ≤ bytes.x.Z
  childLow : slot bytes.x.w 8 ≤ bytes.x.o
  childHigh : bytes.x.o + slot bytes.x.wx 8 + tabBytes bytes.x.wx ≤ bytes.x.Z
  offset : bytes.x.o = qWorkspace
  width48 : bytes.x.wx ≤ 48
  outputPositive : 1 ≤ outputLen
  outputBound : outputLen < 2 ^ 31
  outputWidth : bytes.x.wx = (outputLen + 7) / 8

def CallReducePre (a output : Operand) (p : CallReducePublic) (s : State) : Prop :=
  Good s p.bytes.x.B p.bytes.x.Z p.bytes.x.w p.parentInverse ∧
  ChildReady s.mem p.bytes.x.B p.bytes.x.o p.bytes.x.wx p.modulus p.minv ∧
  (∃ ba : List Byte, OperandBytes s p.bytes.x.B p.bytes.x.Z a ba ∧ ba.length = p.bytes.len) ∧
  pointerValue s.mem p.bytes.x.B a.pointer = p.bytes.ptr ∧
  pointerValue s.mem p.bytes.x.B output.pointer = p.output ∧
  word s.mem p.bytes.x.B output.length.offset = BitVec.ofNat 64 p.outputLen ∧
  (∀ j < p.outputLen, InRegions s.wr (p.output + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.outputLen, p.bytes.x.Z ≤ ofs p.bytes.x.B (p.output + BitVec.ofNat 64 j))

def reduceHead (a output : Operand) : List Instr :=
  Core.operand arg argLen a ++ Core.operand result resultLen output ++ Core.enter qWorkspace

theorem reduceHead_ok {p : CallReducePublic} {s : State} {a output : Operand}
    (ha : pointerFits a.pointer) (ho : pointerFits output.pointer)
    (h : CallReducePre a output p s) :
    WP isa (.block (reduceHead a output)) s (ReduceFinishPre p.toReduceFinishPublic) := by
  obtain ⟨hg, child, ⟨ba, has, hbl⟩, hp, hop, hol, hout, hprefix⟩ := h
  have h256 : 256 ≤ slot p.bytes.x.w 8 := by unfold slot hdrBytes; omega
  have hlo := p.childLow
  have hhi := p.childHigh
  unfold reduceHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments2_ok hg child p.extent (by omega) (by omega) a output ha ho)
    fun u ⟨hgu, hcu, hargs, _, hf, hk⟩ => ?_
  rw [← p.offset]
  refine WP.mono (enter_ok hgu hcu.header p.childLow p.childHigh (by rw [p.offset]; decide))
    fun t ⟨hct, hmem, hkt⟩ => ?_
  have hft : Frm p.bytes.x.B argumentRanges s.mem t.mem := by rw [hmem]; exact hf
  have hkt' : Keep coreRegs s t := (hk.trans hkt).mono (by decide)
  have hargs' : Arguments2 t.mem s.mem p.bytes.x.B a output := hmem ▸ hargs
  have childt : ChildReady t.mem p.bytes.x.B p.bytes.x.o p.bytes.x.wx p.modulus p.minv := hmem ▸ hcu
  refine ⟨⟨⟨⟨hct, ⟨hct.good, childt.modulus, childt.inverse⟩⟩, p.width48⟩,
    ba, hbl, hargs'.1.trans hp, hargs'.2.1.trans has.length, ?_⟩,
    ⟨⟨p.minv, hct, hargs'.2.2.1.trans hop, hargs'.2.2.2.trans hol⟩,
      p.outputPositive, p.outputBound, p.outputWidth, ?_, hprefix⟩⟩
  · rw [← hp]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) has.source
  · intro j hj
    rw [hkt'.2.2]
    exact hout j hj

theorem coreReduce_ct (M : Mont) {a output : Operand}
    (ha : pointerFits a.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (reduceHead a output)) hc).isSome = true) :
    RelCT isa (Two (CallReducePre a output)) (Core.reduce M.mm a output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (reduceHead a output))
    (.seq (Arithmetic.reduce M.mm arg argLen) (seqs Core.finish))) _
  refine RelCT.seq (two_piece (Ψ := fun p s => ReduceFinishPre p.toReduceFinishPublic s) [.rdi]
    (pins_of (fun p _ => p.bytes.x.B) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.1.rdi)) hT (fun _ _ h => reduceHead_ok ha ho h))
    (two_map CallReducePublic.toReduceFinishPublic (fun _ _ h => h) (reduceFinish_ct M))

end VG.Proof.Dsa.X86_64
