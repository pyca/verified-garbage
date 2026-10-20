module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPre
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallRegions
import VerifiedGarbage.Proof.Framework.Block

/-! Calling any verified FFDH backend from the native key-search controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem attemptRun_ok (backend : VG.Proof.Ffdh.Arm.Backend) : AttemptRunOk backend := by
  intro p original s used keys scalars h room
  have facts := h.input.callFacts room
  have rootFit : 184 ≤ p.sp.toNat := h.input.bounds.stackFits
  have outerFit : 32 ≤ s.sp.toNat := by
    rw [h.sp, FrameStack.sub_toNat' (by omega : 24 ≤ p.sp.toNat)]
    omega
  have allocatedFit : (allocated 32 s).sp.toNat + 32 ≤ 2 ^ 32 := by
    change (s.sp - 32#32).toNat + 32 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega
  have control : Controller p.control (allocated 32 s) :=
    ⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)),
      h.pointer⟩
  have stack : Workspace (allocated 32 s) (allocated 32 s).sp 32 :=
    ⟨allocatedFit, List.mem_cons_self⟩
  have separate : (rControl p).Disjoint ⟨State.addr (allocated 32 s).sp, 32⟩ := by
    rw [h.call_sp]
    exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRun
  refine WP.alloc (by decide) outerFit ?_
  rw [WP.seq_iff]
  refine WP.mono (arguments_ok (allocated 32 s) control stack separate h.headers) ?_
  rintro u ⟨⟨args, mem⟩, rest⟩
  have spU : u.sp = callSp p := rest.sp.trans h.call_sp
  have memU : u.mem = callMem p used s.mem (callSp p) := by
    rw [mem, h.call_sp]
    rfl
  refine FrameStack.WP.callF backend.generateKey_verified.1 (call_pre facts args spU memU)
    (h.covers_reads room rest.rd rest.wr) (h.covers_writes rest.wr)
    (by rw [spU]; exact Nat.le_trans backend.keyStack facts.stackFits) ?_
  intro t rd wr sp frame kept post
  refine ⟨h.restore ?_ ?_ ?_ ?_ (h.attempt_frame memU spU frame backend.keyStack), ?_⟩
  · exact rd.trans rest.rd
  · change t.wr.tail = s.wr
    rw [wr, rest.wr]
    rfl
  · change t.sp + 32#32 = s.sp
    rw [sp, rest.sp]
    exact BitVec.sub_add_cancel _ _
  · intro r hr
    change t.gpr r = s.gpr r
    rw [kept r (by revert r hr; decide) (by revert r hr; decide)]
    exact rest.gpr r (by revert r hr; decide)
  · have result := call_post h room args spU memU post
    exact ⟨result.status, result.output⟩

end VG.Proof.Ffdh.Arm.KeySearch
