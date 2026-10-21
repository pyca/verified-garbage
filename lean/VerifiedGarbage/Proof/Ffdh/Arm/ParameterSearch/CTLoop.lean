module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTBranch
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LoopGuard
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost

/-! The complete native loop's timing depends only on its public entropy tape and u64 budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_piece two_post two_taint)

theorem iteration_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    RelCT isa (Two LiveCT) (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate))
      (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.iteration
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) budget_ready) ?_
  refine RelCT.seq (two_post (branch_ct backend) (branch_ready backend)) ?_
  exact two_taint [.r4] (fun _ _ _ hs ht r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact (branch_pointer hs).trans (branch_pointer ht).symm) (by taint_decide)

def CTStep (q : SearchPoint) (s : State) : Prop :=
  if continues q then isa.eval .eq s = some true ∧ LiveCT (nextPoint q) s
  else isa.eval .eq s = some false

theorem ct_step (backend : VG.Proof.Ffdh.Arm.ParameterBackend) (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) s (CTStep q) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.iteration
  refine WP.seq (WP.mono (budget_ready q s h) fun u ready => ?_)
  refine WP.seq (WP.mono (branch_ready backend q u ready) fun t result => ?_)
  by_cases again : continues q
  · simp only [BranchCT, again, ite_true] at result
    refine WP.mono (result.1.loop_guard result.2) ?_
    rintro t ⟨⟨flag, state⟩, _⟩
    simpa only [CTStep, again, ite_true] using (show isa.eval .eq t = some true ∧ LiveCT (nextPoint q) t from ⟨flag, state⟩)
  · simp only [BranchCT, again, ite_false] at result
    obtain ⟨_, finished⟩ := result
    refine WP.mono finished.loop_guard ?_
    rintro t ⟨⟨flag, _⟩, _⟩
    simpa only [CTStep, again, ite_false] using flag

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : SearchPoint, n = q.remaining + 1 ∧ LiveCT q s ∧ LiveCT q t ∧ s.sp = t.sp

private theorem iteration_pair (backend : VG.Proof.Ffdh.Arm.ParameterBackend) (n : Nat) :
    RelCT isa (LoopPair n) (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) fun s t =>
      isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → True) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair m s t) := by
  have wp (q : SearchPoint) (s : State) (h : n = q.remaining + 1 ∧ LiveCT q s) :
      WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) s fun t =>
        n = q.remaining + 1 ∧ CTStep q t :=
    WP.mono (ct_step backend q s h.2) (fun _ result => ⟨h.1, result⟩)
  have ct := two_post ((iteration_ct backend).mono
    (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.2, ht.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, measure, hs, ht, sp⟩ => ⟨q, ⟨measure, hs⟩, ⟨measure, ht⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨measure, hs⟩, ⟨_, ht⟩, sp⟩
  by_cases again : continues q
  · simp only [CTStep, again, ite_true] at hs ht
    refine ⟨hs.1.trans ht.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).remaining + 1, ?_, nextPoint q, rfl, hs.2, ht.2, sp⟩
    have positive := again.1
    change q.remaining - 1 + 1 < n
    omega
  · simp only [CTStep, again, ite_false] at hs ht
    exact ⟨hs.trans ht.symm, fun _ => trivial, fun next => absurd (next.symm.trans hs) (by decide)⟩

theorem loop_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two LiveCT)
    (.loop (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) .eq) (fun _ _ => True) := by
  intro s t traceS traceT u v ⟨q, hs, ht, sp⟩ runS runT
  exact RelCT.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) (c := .eq)
    (Q := fun _ _ => True) LoopPair (iteration_pair backend) (q.remaining + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterSearch
