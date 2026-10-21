module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Loop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Stack
import VerifiedGarbage.Proof.Framework.Block

/-! The complete native search body preserves its caller's registers and writes only its buffers and outgoing stack. -/

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
