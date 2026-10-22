module

public import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Relate a loop whose public iteration count is fixed -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem count_loop_ct {body : Prog isa} {N : Nat} (positive : 0 < N)
    (I : Nat → State → State → Prop)
    (step : ∀ j, j < N → RelCT isa (I j) body fun s t =>
      I (j + 1) s t ∧ s.zf = some (decide (j + 1 = N)) ∧ t.zf = some (decide (j + 1 = N))) :
    RelCT isa (I 0) (.loop body .ne) (I N) := by
  let Inv := fun m s t => ∃ j, m = N - j ∧ j < N ∧ I j s t
  apply (RelCT.loop (M := isa) (Q := I N) Inv ?_ N).mono
  · intro s t h
    exact ⟨0, rfl, positive, h⟩
  · intro _ _ h
    exact h
  · intro m s t tr₁ tr₂ s' t' ⟨j, eq, bound, input⟩ e₁ e₂
    obtain ⟨trace, next, z₁, z₂⟩ := step j bound _ _ _ _ _ _ input e₁ e₂
    refine ⟨trace, ?_, ?_, ?_⟩
    · simp only [eval, z₁, z₂]
    · intro exit
      by_cases last : j + 1 = N
      · simpa only [last] using next
      · simp only [eval, z₁, decide_eq_false last, Option.map_some, Bool.not_false] at exit
        contradiction
    · intro again
      have last : j + 1 ≠ N := by
        intro last
        simp only [eval, z₁, last, decide_true, Option.map_some, Bool.not_true] at again
        contradiction
      exact ⟨N - (j + 1), by omega, j + 1, rfl, by omega, next⟩

end VG.Proof.MillerRabin.X86
