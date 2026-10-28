module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Framework.Omega

/-! The full parameter search uses 24 saved bytes and 24 outgoing bytes above the 184-byte candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem iteration_stack (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterSearch.iteration
      (.call backend.candidateName backend.candidate)) ≤ 208 := by
  have bound := backend.candidateStack
  simp only [VG.Impl.Ffdh.Arm.ParameterSearch.iteration,
    VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep, VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun,
    VG.Impl.Ffdh.Arm.ParameterSearch.classify, VG.Impl.Ffdh.Arm.ParameterSearch.short,
    VG.Impl.Ffdh.Arm.ParameterSearch.exhausted, VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut,
    VG.Impl.Ffdh.Arm.ParameterSearch.request, VG.Impl.Ffdh.Arm.ParameterSearch.select,
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros,
    FrameStack.armStack, Bool.false_eq_true, ite_true, ite_false, Nat.zero_max, Nat.max_zero]
  omega

theorem search_stack (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterSearch.code
      (.call backend.candidateName backend.candidate)) ≤ 232 := by
  have bound := iteration_stack backend
  simp only [VG.Impl.Ffdh.Arm.ParameterSearch.code, VG.Impl.Ffdh.Arm.ParameterSearch.body, FrameStack.armStack,
    List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero]
  omega

end VG.Proof.Ffdh.Arm.ParameterSearch
