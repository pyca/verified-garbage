module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBranch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The native bounded loop's trace is determined by public descriptor,
retry policy and disclosed attempt-status sequence. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

theorem iteration_ct (backend : VG.Proof.Ffdh.Arm.Backend) :
    RelCT isa (Two KeyCTL) (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey))
      (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.iteration
  refine RelCT.seq (two_piece [.r4] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (branch_ct backend) (branch_ready backend))
    (two_taint [.r4] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_pointer h₁).trans (branch_pointer h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval .eq s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval .eq s = some false

theorem ct_step (backend : VG.Proof.Ffdh.Arm.Backend) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) s (KeyCTStep q) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.iteration
  refine WP.seq (WP.mono (keys_ready q s h) fun u ready => ?_)
  refine WP.seq (WP.mono (branch_ready backend q u ready) fun t result => ?_)
  by_cases continues : keyContinues q
  · simp only [KeyBranchResult, continues, ite_true] at result
    obtain ⟨⟨original, live, statuses⟩, word⟩ := result
    rw [← nextKeyPoint_inputs q] at word
    refine WP.mono (live.loop_guard word) ?_
    rintro t ⟨flag, state⟩
    simp only [KeyCTStep, continues, ite_true]
    exact ⟨flag, original, state, statuses⟩
  · simp only [KeyBranchResult, continues, ite_false] at result
    obtain ⟨_, _, finished⟩ := result
    refine WP.mono finished.loop_guard ?_
    rintro t ⟨flag, _⟩
    simp only [KeyCTStep, continues, ite_false]
    exact flag

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (backend : VG.Proof.Ffdh.Arm.Backend) (n : Nat) :
    RelCT isa (LoopPair n) (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) fun s t =>
      isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → True) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair m s t) := by
  have wp (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) s fun t =>
        n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (ct_step backend q s h.2) (fun _ result => ⟨h.1, result⟩)
  have ct := two_post ((iteration_ct backend).mono
    (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q, h₁.2, h₂.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, measure, h₁, h₂, sp⟩ => ⟨q, ⟨measure, h₁⟩, ⟨measure, h₂⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨measure, h₁⟩, ⟨_, h₂⟩, sp⟩
  by_cases continues : keyContinues q
  · simp only [KeyCTStep, continues, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, sp⟩
    have := nextKeyPoint_measure continues
    omega
  · simp only [KeyCTStep, continues, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun again => absurd (again.symm.trans h₁) (by decide)⟩

theorem loop_ct (backend : VG.Proof.Ffdh.Arm.Backend) :
    RelCT isa (Two KeyCTL)
      (.loop (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) .eq) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v ⟨q, h₁, h₂, sp⟩ e₁ e₂
  exact RelCT.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) (c := .eq)
    (Q := fun _ _ => True) LoopPair (iteration_pair backend) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, h₁, h₂, sp⟩ e₁ e₂

end VG.Proof.Ffdh.Arm.KeySearch
