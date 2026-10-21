module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Step
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LoopGuard
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Total correctness of the native safe-prime search loop, with its full u64 attempt measure. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

def SearchInvariant (p : SearchParams) (start : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used remaining, n = remaining + 1 ∧ SearchLive p used remaining s ∧
    expected = p.tail used remaining ∧ Rest searchClobbers start s

def SearchFinished (p : SearchParams) (start : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (s : State) : Prop := SearchDone p expected s ∧ Rest searchClobbers start s

theorem iteration (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {start s : State} {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (inv : SearchInvariant p start expected n s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) s fun t =>
      (isa.eval .eq t = some false ∧ SearchFinished p start expected t) ∨
      (isa.eval .eq t = some true ∧ ∃ m < n, SearchInvariant p start expected m t) := by
  obtain ⟨used, remaining, measure, h, same, initialRest⟩ := inv
  have done : ∀ t, SearchDone p expected t → Rest searchClobbers start t →
      WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 13, .cmp .r9 (.imm 4)]) t fun t =>
        (isa.eval .eq t = some false ∧ SearchFinished p start expected t) ∨
        (isa.eval .eq t = some true ∧ ∃ m < n, SearchInvariant p start expected m t) := by
    intro t finished rest
    refine WP.mono finished.loop_guard ?_
    rintro u ⟨⟨flag, result⟩, restU⟩
    exact Or.inl ⟨flag, result, rest.trans (restU.mono (by simp [searchClobbers]))⟩
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.iteration
  refine WP.seq (WP.mono h.budget_guard fun u ⟨⟨liveU, flag, _⟩, restU⟩ => ?_)
  have restSU : Rest searchClobbers start u := initialRest.trans (restU.mono (by simp [searchClobbers]))
  apply WP.seq
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono liveU.exhausted ?_
    rintro t ⟨finished, restT⟩
    have result : expected = .exhausted used := by rw [same, zero']; rfl
    rw [← result] at finished
    exact done t finished (restSU.trans restT)
  · intro nonzero
    have positive : 0 < remaining := Nat.pos_of_ne_zero (of_decide_eq_false nonzero)
    refine WP.mono (liveU.step backend positive) ?_
    rintro t ⟨classified, restT⟩
    have restST := restSU.trans restT
    cases result : candidateResult p used with
    | none =>
      simp only [Classified, result] at classified
      rw [← same] at classified
      exact done t classified restST
    | some pair =>
      obtain ⟨prime, rand⟩ := pair
      cases prime with
      | some prime =>
        simp only [Classified, result] at classified
        rw [← same] at classified
        exact done t classified restST
      | none =>
        simp only [Classified, result] at classified
        refine WP.mono (classified.1.loop_guard classified.2) ?_
        rintro q ⟨⟨flagQ, liveQ⟩, restQ⟩
        refine Or.inr ⟨flagQ, remaining, by omega, used + candidateUsed p used, remaining - 1,
          by omega, liveQ, same.trans (p.tail_reject positive result),
          restST.trans (restQ.mono (by simp [searchClobbers]))⟩

theorem loop (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {start s : State} {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (inv : SearchInvariant p start expected n s) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) .eq)
      s (SearchFinished p start expected) :=
  WP.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) (c := .eq)
    (Q := SearchFinished p start expected) (SearchInvariant p start expected)
    (fun _ _ h => iteration backend h) n s inv

end VG.Proof.Ffdh.Arm.ParameterSearch
