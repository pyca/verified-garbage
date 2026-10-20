module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The precomputation entry only retains arguments at fixed public stack offsets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private theorem combEntryArgs_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.entryArgs) LocalAddress := by
  change RelCT isa _ (.block ([.addSp .r12 0] ++ [.str .r0 .r12 4,.str .r2 .r12 24,
    .str .r3 .r12 28,.ldrSp .r3 128,.str .r3 .r12 32,.ldrSp .r0 132,.str .r0 .r12 0])) _
  have tail := RelCT.block_append ((loadLocal_ct .r0 132 (by decide)).seq (storeLocal_ct .r0 0))
  have tail := RelCT.block_append ((storeLocal_ct .r3 32).seq tail)
  have tail := RelCT.block_append ((loadLocal_ct .r3 128 (by decide)).seq tail)
  have tail := RelCT.block_append ((storeLocal_ct .r3 28).seq tail)
  have tail := RelCT.block_append ((storeLocal_ct .r2 24).seq tail)
  have tail := RelCT.block_append ((storeLocal_ct .r0 4).seq tail)
  exact RelCT.block_append (stackAddr_ct.seq tail)

private theorem combPrepareArgs_ct : RelCT isa LocalAddress
    (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) LocalAddress := by
  change RelCT isa _ (.block ([.ldrSp .r4 24] ++ [.ldrSp .r6 32,.addSp .r12 0,
    .str .r4 .r12 8,.str .r6 .r12 12])) _
  exact RelCT.block_append ((loadLocal_ct .r4 24 (by decide)).seq
    (RelCT.block_append ((loadLocal_ct .r6 32 (by decide)).seq
    (RelCT.block_append ((stackAddr_ct.mono (fun _ _ h => h.2) (fun _ _ h => h)).seq
    (RelCT.block_append ((storeLocal_ct .r4 8).seq (storeLocal_ct .r6 12))))))))

theorem combEntry_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) (fun _ _ => True) := by
  have pointers : RelCT isa LocalAddress (.block VG.Impl.Ffdh.Arm.Domain.domainPointers) (fun _ _ => True) := by
    apply RelCT.taint (A:=VG.Arm.taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.entry
  exact RelCT.block_append ((RelCT.block_append (combEntryArgs_ct.seq combPrepareArgs_ct)).seq pointers)

end VG.Proof.Ffdh.Arm
