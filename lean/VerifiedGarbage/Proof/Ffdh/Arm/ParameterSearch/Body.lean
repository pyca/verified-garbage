module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Loop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
/-! The complete native search body preserves its caller's registers and writes only its buffers and outgoing stack. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Stack.lean`, which only this module imported.
section

/-! The full parameter search uses 24 saved bytes and 24 outgoing bytes above the 184-byte candidate. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

def bodyClobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r9, .r10, .r11, .r12, .lr]

theorem body_ok (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : SearchStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s fun t =>
      SearchDone p (p.tail 0 p.attempts) t ∧ Rest bodyClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.body
  refine WP.seq (WP.mono h.entry fun u ⟨live, rest⟩ => ?_)
  have inv : SearchInvariant p u (p.tail 0 p.attempts) (p.attempts + 1) u :=
    ⟨0, p.attempts, rfl, live, rfl, Rest.refl _ _⟩
  refine WP.mono (loop backend inv) ?_
  rintro t ⟨finished, restT⟩
  exact ⟨finished, (rest.mono (by simp [bodyClobbers])).trans (restT.mono (by simp [bodyClobbers, searchClobbers]))⟩

theorem body_run (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : SearchStart p s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s tr t ∧
      SearchDone p (p.tail 0 p.attempts) t ∧ Rest bodyClobbers s t ∧
      Frame (s.wr ++ [FrameStack.belowA s.sp 208]) s.mem t.mem := by
  obtain ⟨tr, t, run, done, rest⟩ := body_ok backend h
  have bound : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterSearch.body
      (.call backend.candidateName backend.candidate)) ≤ 208 := by
    simpa only [VG.Impl.Ffdh.Arm.ParameterSearch.body, FrameStack.armStack, Nat.zero_max] using iteration_stack backend
  have fit : 208 ≤ s.sp.toNat := h.storage.below
  exact ⟨tr, t, run, done, rest, FrameStack.Frame.belowA_mono (FrameStack.Exec.frameSp run (Nat.le_trans bound fit)) bound fit⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
