module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallConsts
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallRegions
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated

/-! Calling any verified FFDH backend from the native key-search controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem attemptRun_ok (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : AttemptRunOk backend := by
  intro p original s used keys scalars h room
  have facts := h.input.callFacts room
  have rootFit : stackUse sampling ≤ p.sp.toNat := h.input.bounds.stackFits
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at rootFit
  have outerFit : sampling.argumentBytes ≤ s.sp.toNat := by
    rw [h.sp, FrameStack.sub_toNat' (by omega : 24 ≤ p.sp.toNat)]
    omega
  have allocatedFit : (allocated sampling.argumentBytes s).sp.toNat + sampling.argumentBytes ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 sampling.argumentBytes).toNat + sampling.argumentBytes ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega
  have control : Controller p.control (allocated sampling.argumentBytes s) :=
    ⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)),
      h.pointer⟩
  have stack : Workspace (allocated sampling.argumentBytes s) (allocated sampling.argumentBytes s).sp sampling.argumentBytes :=
    ⟨allocatedFit, List.mem_cons_self⟩
  have separate : (rControl p).Disjoint ⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩ := by
    rw [h.call_sp]
    exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor
  change WP isa (.frame (.alloc sampling.argumentBytes) (.seq (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) (.call backend.keyName backend.generateKey)) (.free sampling.argumentBytes)) s _
  refine WP.alloc (by cases sampling <;> decide) outerFit ?_
  rw [WP.seq_iff]
  refine WP.mono_syms (arguments_ok (allocated sampling.argumentBytes s) control stack separate h.headers h.cachedSlots) ?_
  rintro u ⟨⟨args, mem⟩, rest⟩ symsU
  have spU : u.sp = callSp p := rest.sp.trans h.call_sp
  have memU : u.mem = callMem p used s.mem (callSp p) := by
    rw [mem, h.call_sp]
    rfl
  apply WP.of_syms
  refine FrameStack.WP.callF backend.generateKey_verified.1 (call_pre h room args spU memU symsU)
    (h.covers_reads room rest.rd rest.wr) (h.covers_writes rest.wr)
    (by rw [spU]; exact Nat.le_trans backend.keyStack facts.stackFits) ?_
  intro t rd wr sp frame kept post symsT
  refine ⟨h.restore ?_ ?_ ?_ ?_ (symsT.trans symsU) (h.attempt_frame memU spU frame backend.keyStack), ?_⟩
  · exact rd.trans rest.rd
  · change t.wr.tail = s.wr
    rw [wr, rest.wr]
    rfl
  · change t.sp + BitVec.ofNat 32 sampling.argumentBytes = s.sp
    rw [sp, rest.sp]
    exact BitVec.sub_add_cancel _ _
  · intro r hr
    change t.gpr r = s.gpr r
    rw [kept r (by revert r hr; decide) (by revert r hr; decide)]
    exact rest.gpr r (by revert r hr; decide)
  · have result := call_post h room args spU memU (selected_attempt_post.mp post)
    exact ⟨result.status, result.output⟩

end VG.Proof.Ffdh.Arm.KeySearch
