module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! # Witness cursors name exact suffixes, not merely equal-length lists -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Spec.RsaKeyGen

theorem loop_suffix {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    (hstep : ∀ s r x r', step s r = some (x, r') → r' <:+ r) :
    ∀ s r a r', loop step s r = some (a, r') → r' <:+ r := by
  intro s r
  induction r using (measure List.length).wf.induction generalizing s with
  | h r ih =>
    intro a r' h
    rw [loop] at h
    split at h
    · cases h
    · cases h
      exact hstep _ _ _ _ (by assumption)
    · split at h
      · rename_i hlt
        exact (ih _ hlt _ _ _ h).trans (hstep _ _ _ _ (by assumption))
      · cases h

theorem draw_suffix_of_result {n : Nat} {r : Rand} {x : Nat} {r' : Rand}
    (h : draw n r = some (x, r')) : r' <:+ r := by
  unfold draw at h
  simp only at h
  split at h
  · cases h; exact List.drop_suffix _ _
  · cases h

theorem mrStep_suffix {c ch a m : Nat} :
    ∀ (s : Nat × Nat) (r : Rand) x r', mrStep c ch a m s r = some (x, r') → r' <:+ r := by
  intro s r x r' hs
  obtain ⟨i, u⟩ := s
  unfold mrStep at hs
  simp only at hs
  by_cases hg : i ≤ blindedChecks ∨ u < ch
  · rw [ite_eq_left hg] at hs
    rcases hd : draw (witnessBytes c) r with _ | ⟨y, r₁⟩
    · simp [hd] at hs
    · simp only [hd, Option.bind_eq_bind, Option.bind_some] at hs
      have hrest := draw_suffix_of_result hd
      by_cases hm : mrIteration c a m (witness (c - 1) y).1 = true <;>
        simp only [hm, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true] at hs <;>
        (obtain ⟨-, rfl⟩ := hs; exact hrest)
  · rw [ite_eq_right hg] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact List.suffix_refl _

theorem probablePrime_suffix {w : Nat} {r rest : Rand} {b : Bool}
    (h : Spec.Dsa.probablePrime w r = some (b, rest)) : rest <:+ r := by
  unfold Spec.Dsa.probablePrime at h
  split at h
  · cases h; exact List.suffix_refl _
  · split at h
    · cases h; exact List.suffix_refl _
    · split at h
      · cases h; exact List.suffix_refl _
      · split at h
        · cases h; exact List.suffix_refl _
        · exact loop_suffix mrStep_suffix _ _ _ _ h

theorem suffix_drop_length {r rest : Rand} (h : rest <:+ r) :
    r.drop (r.length - rest.length) = rest := by
  obtain ⟨front, rfl⟩ := h
  simp

theorem probablePrime_cursor {w used : Nat} {r rest : Rand} {b : Bool}
    (h : Spec.Dsa.probablePrime w (r.drop used) = some (b, rest)) :
    r.drop (r.length - rest.length) = rest :=
  suffix_drop_length ((probablePrime_suffix h).trans (List.drop_suffix _ _))

end VG.Proof.Dsa.Generation
