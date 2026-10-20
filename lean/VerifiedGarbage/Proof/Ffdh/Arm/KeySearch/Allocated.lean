module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! Geometry of the nested call's allocated argument frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem KeyLive.allocated_data {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Controller p.control (allocated 32 s) ∧ Workspace (allocated 32 s) (allocated 32 s).sp 32 ∧
      (rControl p).Disjoint (rArguments p) := by
  have rootFit : 184 ≤ p.sp.toNat := h.input.bounds.stackFits
  have outerFit : 32 ≤ s.sp.toNat := by
    rw [h.sp, FrameStack.sub_toNat' (by omega : 24 ≤ p.sp.toNat)]; omega
  refine ⟨⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)), h.pointer⟩,
    ⟨?_, List.mem_cons_self⟩, ?_⟩
  · change (s.sp - 32#32).toNat + 32 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega
  · exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm

end VG.Proof.Ffdh.Arm.KeySearch
