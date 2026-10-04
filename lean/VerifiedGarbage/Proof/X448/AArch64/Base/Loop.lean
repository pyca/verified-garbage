import VerifiedGarbage.Proof.X448.AArch64.Base.Step

/-!
# X448 of the base point on AArch64: the comb's loop

Untrusted: everything here is checked by Lean. The 56 steps take `StepInv` from
`j` to 56.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64

theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 56 → StepInv s₀ base k (56 - n) s →
      WP isa (.loop VG.Impl.X448.AArch64.Base.step (.nonzero .x .x9)) s fun t => StepInv s₀ base k 56 t := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Base.step) (c := .nonzero .x .x9)
    (Q := fun t => StepInv s₀ base k 56 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 56 ∧ StepInv s₀ base k (56 - m) s) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (step_ok hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨by decide, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_⟩
    rw [show 56 - (m - 1) = 56 - m + 1 by omega]
    exact ht

end VG.Proof.X448.AArch64.Base
