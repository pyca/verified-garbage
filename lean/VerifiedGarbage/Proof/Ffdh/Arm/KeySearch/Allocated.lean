module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! Geometry of the nested call's allocated argument frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm

theorem KeyLive.allocated_data {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Controller p.control (allocated sampling.argumentBytes s) ∧ Workspace (allocated sampling.argumentBytes s) (allocated sampling.argumentBytes s).sp sampling.argumentBytes ∧
      (rControl p).Disjoint (rArguments p) := by
  have rootFit : stackUse sampling ≤ p.sp.toNat := h.input.bounds.stackFits
  have outerFit : sampling.argumentBytes ≤ s.sp.toNat := by
    have size := argumentBytes_max sampling
    have total := stackUse_min sampling
    rw [h.sp, FrameStack.sub_toNat' (by omega : 24 ≤ p.sp.toNat)]; omega
  refine ⟨⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)), h.pointer⟩,
    ⟨?_, List.mem_cons_self⟩, ?_⟩
  · change (s.sp - BitVec.ofNat 32 sampling.argumentBytes).toNat + sampling.argumentBytes ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega
  · exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm

theorem KeyLive.call_sp {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    (allocated sampling.argumentBytes s).sp = callSp p := by
  change s.sp - BitVec.ofNat 32 sampling.argumentBytes = callSp p
  rw [h.sp, BitVec.sub_sub, ← BitVec.ofNat_add]

end VG.Proof.Ffdh.Arm.KeySearch
