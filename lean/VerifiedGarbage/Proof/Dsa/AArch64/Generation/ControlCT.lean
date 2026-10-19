module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! Compose a public branch with its common continuation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem ite_seq_ct {P Q : State → State → Prop} {c : isa.Cond} {t e k : Prog isa}
    (hc : ∀ s₁ s₂, P s₁ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some true) (.seq t k) Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some false) (.seq e k) Q) :
    RelCT isa P (.seq (.ite c t e) k) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hce := hc _ _ hp
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases a₁ with
      | iteT c₁ x₁ =>
        cases a₂ with
        | iteT _ x₂ =>
          obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ (.seq x₁ b₁) (.seq x₂ b₂)
          exact ⟨by simpa using ht', hq⟩
        | iteF c₂ _ => rw [hce, c₂] at c₁; cases c₁
      | iteF c₁ x₁ =>
        cases a₂ with
        | iteT c₂ _ => rw [hce, c₂] at c₁; cases c₁
        | iteF _ x₂ =>
          obtain ⟨ht', hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ (.seq x₁ b₁) (.seq x₂ b₂)
          exact ⟨by simpa using ht', hq⟩

/-- `RelCT.ite_seq` for runs that agree on the public data, which fixes the
condition. -/
theorem two_ite_seq {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el k : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) (.seq th k) Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) (.seq el k) Q) :
    RelCT isa (Two Φ) (.seq (.ite cond th el) k) Q := by
  refine ite_seq_ct (fun _ _ ⟨a, h₁, h₂, hsp⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h) (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

end VG.Proof.Dsa.AArch64.Generation
