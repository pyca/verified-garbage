module

public import VerifiedGarbage.Proof.Framework.RelCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Reassociating a sequence in a relational timing proof, on any ISA -/

@[expose] public section

namespace VG.Proof.Dsa

variable {M : ISA}

theorem RelCT.assoc' {P Q : M.State → M.State → Prop} {a b c : Prog M}
    (h : RelCT M P (.seq a (.seq b c)) Q) : RelCT M P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

end VG.Proof.Dsa
