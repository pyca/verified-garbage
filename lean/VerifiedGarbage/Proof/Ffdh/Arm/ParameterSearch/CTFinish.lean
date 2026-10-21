module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LoopGuard
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Finish
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The return path writes a fixed public consumption pointer and reads fixed saved-register offsets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_taint two_post lowWord)

def FinishPointer (p : SearchParams) (s : State) : Prop := s.gpr .r4 = p.control ∧ s.gpr .r1 = p.c.usedPtr

private theorem finish_pointer (p : SearchParams) (s : State) (h : DoneCT p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6]) s (FinishPointer p) := by
  obtain ⟨_, done⟩ := h
  have pointer := done.usedPtr
  have context := done.buffers.controller
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord FinishPointer at *
  ffrun [context.addr (by decide : 6 < 16), context.read (by decide : 6 < 16), pointer]
  exact context.ptr

theorem finish_ct : RelCT isa (Two DoneCT) (.block VG.Impl.Ffdh.Arm.ParameterSearch.finish) (fun _ _ => True) := by
  change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6] ++
    ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13,
      .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] ++
      finishRestoreSlots.map (fun e => Instr.ldrSp e.1 e.2)))) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.r4] done_pins (by taint_decide)) finish_pointer) ?_)
  refine RelCT.block_append (RelCT.seq (relCT_keep_sp
    (two_taint [.r4, .r1] (fun _ _ _ hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)) (fun _ _ ⟨_, _, _, sp⟩ => sp)) ?_)
  exact (stackLoads_ct finishRestoreSlots).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.ParameterSearch
