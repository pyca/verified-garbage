module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Relating two runs, on any ISA

Untrusted: everything here is checked by Lean. As
`Proof/Gather/RISCV64/LoopCT.lean` does for RISC-V: two runs from `σ₁` and
`σ₂` (`Eq2`) leak the same trace through `c₁` then `c₂` if they do through
`c₁`, and through `c₂` from any states the correctness proofs of `c₁`
describe (`rel_seq`); `ct_of` makes constant time of it.
-/

@[expose] public section

namespace VG.Proof.Xdh

open VG

variable {M : ISA}

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : M.State) (a b : M.State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : M.State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog M} {σ₁ σ₂ : M.State} {F₁ F₂ : M.State → Prop}
    (h₁ : RelCT M (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP M c₁ σ₁ F₁) (w₂ : WP M c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT M (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT M (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem ct_of {pre : M.State → Prop} {pub : M.State → M.State → Prop} {c : Prog M}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT M (Eq2 σ₁ σ₂) c TT) : ConstantTime M pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Xdh
