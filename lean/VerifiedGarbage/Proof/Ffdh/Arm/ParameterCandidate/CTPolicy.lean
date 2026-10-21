module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLocalBlock
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Public phase setup and sieve flags write only fixed local-frame addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm

theorem save_ct (r : Reg) (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.save r slot)) (fun s t => s.sp = t.sp) :=
  RelCT.block_append (stackAddr_ct.seq ((localBlock_ct [.str r .r12 slot] rfl).mono
    (fun _ _ h => h) (fun _ _ h => h.2)))

theorem saveWord_ct (r : Reg) (slot : Nat) (value : BitVec 32) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (([.mov r (.imm value)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save r slot)) (fun s t => s.sp = t.sp) :=
  RelCT.block_append ((stackOnly_ct [.mov r (.imm value)] rfl).seq (save_ct r slot))

private def phaseRead (q : Bool) : List Instr := [.ldrSp .r3 24] ++
  if q then [.dp .sub .r3 .r3 (.imm 1)] else []

private def phaseTail : List Instr := [.str .r3 .r12 44] ++ VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth ++
  VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks ++ VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed

theorem phaseHead_ct (q : Bool) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) (fun s t => s.sp = t.sp) := by
  have read : RelCT isa (fun s t => s.sp = t.sp) (.block (phaseRead q)) (fun s t => s.sp = t.sp) :=
    stackOnly_ct _ (by cases q <;> decide)
  have tail : RelCT isa LocalAddress (.block phaseTail) (fun s t => s.sp = t.sp) :=
    (localBlock_ct _ (by decide)).mono (fun _ _ h => h) (fun _ _ h => h.2)
  have trace := RelCT.block_append (read.seq (RelCT.block_append (stackAddr_ct.seq tail)))
  cases q <;> exact trace

theorem sieveFlag_ct : RelCT isa (fun s t => s.sp = t.sp ∧ s.z = t.z)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag (fun s t => s.sp = t.sp) := by
  refine RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.2]) ?_ ?_
  · exact (saveWord_ct .r1 64 1).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ h => h.1.1)

end VG.Proof.Ffdh.Arm.ParameterCandidate
