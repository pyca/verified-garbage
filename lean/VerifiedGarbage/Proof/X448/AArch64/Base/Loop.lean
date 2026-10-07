import VerifiedGarbage.Proof.X448.AArch64.Base.Step

/-!
# X448 of the base point on AArch64: the comb's loop

Untrusted: everything here is checked by Lean. The steps of a comb of `n` tables
take `StepInv` from `j` to `n`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64

theorem loop_ok {n : Nat} (hn : n ≤ 57) {s₀ : State} {base : Addr} {k : Nat} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ n → StepInv n s₀ base k (n - m) s → s.syms = s₀.syms →
      WP isa (.loop (VG.Impl.X448.AArch64.Base.stepN n) (.nonzero .x .x9)) s fun t =>
        StepInv n s₀ base k n t := by
  intro m s h1 h2 hi hsy
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Base.stepN n) (c := .nonzero .x .x9)
    (Q := fun t => StepInv n s₀ base k n t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ StepInv n s₀ base k (n - m) s ∧ s.syms = s₀.syms) ?_ m s
    ⟨h1, h2, hi, hsy⟩
  intro m s ⟨h1, h2, hi, hsy⟩
  refine WP.mono_syms (step_ok hn hi (by omega) hsy) fun t ⟨hz, ht⟩ tsy => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    rw [show n - 1 + 1 = n by omega] at ht ⊢
    exact .inl ⟨by simp, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_,
      tsy.trans hsy⟩
    rw [show n - (m - 1) = n - m + 1 by omega]
    exact ht

end VG.Proof.X448.AArch64.Base
