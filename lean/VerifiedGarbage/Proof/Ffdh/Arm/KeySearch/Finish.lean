module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset

/-! The native controller writes its result and restores the complete AAPCS
callee-saved register set before its final frame pop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def finishRestoreSlots : List (Reg × Nat) := [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]

theorem finish_ok {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.finish) s fun t =>
      abiPreserved original (popped .r4 24 t) ∧ ResultPost p result (popped .r4 24 t) := by
  change WP isa (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] ++
    finishRestoreSlots.map (fun e => Instr.ldrSp e.1 e.2))) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishHead_ok s h.controller h.used_buffer h.usedPtr h.used h.status) ?_
  rintro u ⟨⟨status, mem⟩, rest⟩
  have frame : Frame [rUsed p] s.mem u.mem := by rw [mem]; exact usedMem_frame _ _ _
  have saved : Spill.Saved u.mem (State.addr u.sp) original.gpr savedSlots := by
    rw [rest.sp, h.sp]
    apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.saved_used
  have read : InRegions (u.rd ++ u.wr) (State.addr u.sp) 24 := by
    refine ⟨⟨State.addr u.sp, 24⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [rest.wr, rest.sp, h.sp, h.wr]
    exact List.mem_cons_self
  have fit : u.sp.toNat + 24 ≤ 2 ^ 32 := by
    rw [rest.sp, h.sp, FrameStack.sub_toNat' (by have := h.input.bounds.stackFits; change 184 ≤ p.sp.toNat at this; omega)]
    have := p.sp.isLt
    omega
  refine WP.mono (restoreSlots_ok finishRestoreSlots u original.gpr (by decide) fit read
    (by intro e he
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (by intro e he
        apply saved e
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp [savedSlots])) ?_
  rintro t ⟨restored, memT, restT⟩
  have popped4 : (popped .r4 24 t).gpr .r4 = original.gpr .r4 := by
    change t.mem.readW (State.addr t.sp) 32 = _
    rw [memT, restT.sp]
    simpa only [BitVec.add_zero] using saved (.r4, 0) (by simp [savedSlots])
  have kept (r : Reg) (member : r ∈ [.r5, .r6, .r7, .r8]) :
      (popped .r4 24 t).gpr r = original.gpr r := by
    rw [popped_gpr (by revert r member; decide)]
    exact (restT.gpr r (by revert r member; decide)).trans
      ((rest.gpr r (by revert r member; decide)).trans (h.kept r member))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact popped4
    · exact kept .r5 (by simp)
    · exact kept .r6 (by simp)
    · exact kept .r7 (by simp)
    · exact kept .r8 (by simp)
    · rw [popped_gpr (by decide : Reg.r9 ≠ .r4)]; exact restored (.r9, 4) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r10 ≠ .r4)]; exact restored (.r10, 8) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r11 ≠ .r4)]; exact restored (.r11, 12) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.lr ≠ .r4)]; exact restored (.lr, 20) (by simp [finishRestoreSlots])
  · rw [popped_sp, restT.sp, rest.sp, h.sp, BitVec.sub_add_cancel]
    rw [← h.input.2]
    rfl
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r4)]
    exact (restT.gpr .r0 (by simp [finishRestoreSlots])).trans status
  · rw [popped_mem, memT]
    exact h.output_after_used frame
  · rw [popped_mem, memT]
    exact (h.policy_after_used frame).trans h.policy
  · rw [popped_mem, memT, mem]
    exact usedMem_words _ _ _ (by have := h.used_le; have := h.input.bounds.randomFits; omega)

end VG.Proof.Ffdh.Arm.KeySearch
