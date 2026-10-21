module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLeaf
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Step
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Exit
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The exact next public search point is fixed by the tape and complete retry counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_ite)

def continues (q : SearchPoint) : Prop := q.remaining ≠ 0 ∧
  match candidateResult q.inputs q.used with | some (none, _) => True | _ => False

instance (q : SearchPoint) : Decidable (continues q) := by
  unfold continues
  cases candidateResult q.inputs q.used with
  | none => infer_instance
  | some pair => obtain ⟨prime, rand⟩ := pair; cases prime <;> infer_instance

def nextPoint (q : SearchPoint) : SearchPoint :=
  ⟨q.inputs, q.used + candidateUsed q.inputs q.used, q.remaining - 1⟩

def BranchCT (q : SearchPoint) (s : State) : Prop :=
  if continues q then LiveCT (nextPoint q) s ∧ VG.Proof.Ffdh.Arm.KeySearch.lowWord s.mem q.inputs.control 13 = 4#32
  else DoneCT q.inputs s

def BudgetCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧
  isa.eval .eq s = some (decide (q.remaining = 0))

theorem budget_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
      VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard)) s (BudgetCT q) := by
  refine WP.mono h.budget_guard ?_
  rintro t ⟨⟨live, flag, _⟩, _⟩
  exact ⟨live, by change some t.z = _; rw [flag]⟩

theorem branch_pointer {q : SearchPoint} {s : State} (h : BranchCT q s) : s.gpr .r4 = q.inputs.control := by
  by_cases again : continues q
  · simp only [BranchCT, again, ite_true] at h
    exact h.1.buffers.controller.ptr
  · simp only [BranchCT, again, ite_false] at h
    obtain ⟨_, done⟩ := h
    exact done.buffers.controller.ptr

theorem branch_ready (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    (q : SearchPoint) (s : State) (h : BudgetCT q s) :
    WP isa (.ite .eq VG.Impl.Ffdh.Arm.ParameterSearch.exhausted
      (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate))) s (BranchCT q) := by
  refine WP.ite _ h.2 ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    have stop : ¬ continues q := by simp [continues, zero']
    refine WP.mono h.1.exhausted ?_
    rintro t ⟨done, _⟩
    exact (by simpa only [BranchCT, stop, ite_false] using (show DoneCT q.inputs t from ⟨_, done⟩))
  · intro nonzero
    have nonzero' := of_decide_eq_false nonzero
    refine WP.mono (h.1.step backend (Nat.pos_of_ne_zero nonzero')) ?_
    rintro t ⟨data, _⟩
    cases result : candidateResult q.inputs q.used with
    | none =>
      have stop : ¬ continues q := by simp [continues, result]
      simp only [Classified, result] at data
      simpa only [BranchCT, stop, ite_false] using (show DoneCT q.inputs t from ⟨_, data⟩)
    | some pair =>
      obtain ⟨prime, rand⟩ := pair
      cases prime with
      | none =>
        have again : continues q := by simp [continues, nonzero', result]
        simpa only [Classified, result, BranchCT, again, ite_true, LiveCT, nextPoint] using data
      | some prime =>
        have stop : ¬ continues q := by simp [continues, result]
        simp only [Classified, result] at data
        simpa only [BranchCT, stop, ite_false] using (show DoneCT q.inputs t from ⟨_, data⟩)

theorem branch_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    RelCT isa (Two BudgetCT) (.ite .eq VG.Impl.Ffdh.Arm.ParameterSearch.exhausted
      (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate))) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact exhausted_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
      ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1⟩, ⟨q.used, q.remaining, ht.1.1⟩, sp⟩) (fun _ _ h => h)
  · exact (step_ct backend).mono (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterSearch
