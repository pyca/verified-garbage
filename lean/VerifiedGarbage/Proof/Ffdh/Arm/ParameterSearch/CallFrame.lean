module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPreserves
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Arguments
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Argument stores and candidate stack writes stay below the search's saved frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem argument_frame {p : SearchParams} {used : Nat} {s u : State}
    (h : SearchBuffers p s) (mem : u.mem = callMem p used s.mem (s.sp - 24#32)) :
    Frame (callChanges p s.sp) s.mem u.mem := by
  rw [mem]
  apply (callMem_frame p used s.mem (s.sp - 24#32)).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [callChanges], callArguments_sub h.below⟩

theorem candidate_frame {p : SearchParams} {s u t : State} {depth : Nat}
    (h : SearchBuffers p s) (sp : u.sp = s.sp - 24#32) (limit : depth ≤ 184)
    (frame : Frame (callWr p ++ [FrameStack.belowA u.sp depth]) u.mem t.mem) :
    Frame (callChanges p s.sp) u.mem t.mem := by
  apply frame.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals exact ⟨_, by simp [callChanges], fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨FrameStack.belowA s.sp 208, by simp [callChanges], ?_⟩
    rw [sp]
    exact fun a ha => callStack_sub h.below a
      (FrameStack.belowA_sub limit (callStack_fits h.below) a ha)

end VG.Proof.Ffdh.Arm.ParameterSearch
