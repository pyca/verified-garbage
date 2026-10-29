module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FinishMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch

import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.TCB.Code
/-! The native controller writes its result and restores the complete AAPCS
callee-saved register set before its final frame pop. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/FinishHead.lean`, which only this module imported.
section

/-! The controller returns its status and writes a full u64 entropy-consumption count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord usedMem)

theorem finishHead_ok (s : State) {base ptr : BitVec 32} {count status : Nat}
    (h : Controller base s) (output : OutputBuffer ptr 8 s)
    (pointer : lowWord s.mem base 6 = ptr) (used : lowWord s.mem base 4 = BitVec.ofNat 32 count)
    (result : lowWord s.mem base 13 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧ t.mem = usedMem s.mem ptr (BitVec.ofNat 32 count)) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3] ?_ (by rfl) (by rfl)
  have write0 : InRegions s.wr (State.addr ptr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr ptr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (ptr + 4#32) = off (State.addr ptr) 4 := VG.Arm.addr_add (by have := output.fits; omega)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord usedMem at *
  ffrun [h.addr (by decide : 6 < 16), h.addr (by decide : 4 < 16), h.addr (by decide : 13 < 16),
    h.read (by decide : 6 < 16), h.read (by decide : 4 < 16), h.read (by decide : 13 < 16),
    pointer, used, result, BitVec.add_zero, addr4, write0, write4]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (usedMem_frame usedMem_words)

def finishRestoreSlots : List (Reg × Nat) := [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]

theorem finish_ok {p : SearchParams} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : FinishInput p original result s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.finish) s fun t =>
      abiPreserved original (popped .r4 24 t) ∧ ResultPost p result (popped .r4 24 t) := by
  change WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4,
    VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] ++
    finishRestoreSlots.map (fun e => Instr.ldrSp e.1 e.2))) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishHead_ok s h.buffers.controller h.toSearchDone.used_buffer h.usedPtr h.used h.status) ?_
  rintro u ⟨⟨status, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem u.mem := by rw [mem]; exact usedMem_frame _ _ _
  have saved : Spill.Saved u.mem (State.addr u.sp) original.gpr savedSlots := by
    rw [rest.sp]
    apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simpa only [BitVec.add_zero, Nat.sub_zero] using
      (h.buffers.stackSeparate ⟨State.addr p.c.usedPtr, 8⟩ (by simp)).1
  have read : InRegions (u.rd ++ u.wr) (State.addr u.sp) 24 := by
    rw [rest.rd, rest.wr, rest.sp]
    exact h.buffers.stack
  have fit : u.sp.toNat + 24 ≤ 2 ^ 32 := by
    rw [rest.sp, h.sp, FrameStack.sub_toNat' h.stackFits]
    have := original.sp.isLt
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
    rw [popped_gpr (by cases r <;> simp_all [finishRestoreSlots])]
    exact (restT.gpr r (by cases r <;> simp_all [finishRestoreSlots])).trans
      ((rest.gpr r (by cases r <;> simp_all [finishRestoreSlots])).trans (h.kept r member))
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
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r4)]
    exact (restT.gpr .r0 (by simp [finishRestoreSlots])).trans status
  · rw [popped_mem, memT]
    exact h.toSearchDone.output_after_used frame
  · rw [popped_mem, memT, mem]
    exact usedMem_words _ _ _ (by have := h.usedBound; have := p.c.tapeCount; omega)
  · rw [popped_mem, memT]
    exact h.toSearchDone.policy_after_used frame

end VG.Proof.Ffdh.Arm.ParameterSearch
