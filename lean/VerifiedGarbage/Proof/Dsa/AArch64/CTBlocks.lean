module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.Run


/-! # Timing-preserving composition of adjacent DSA instruction blocks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
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

theorem splitBlock_exec {a b : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (a ++ b)) s tr t) : Exec isa (.seq (.block a) (.block b)) s tr t := by
  rw [Exec.block_iff, execBlock_append, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := h
  rw [Option.map_eq_some_iff] at h₂
  obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact .seq (.block h₁) (.block h₂)

theorem fuseBlocks_ct {P Q : State → State → Prop} {a b : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) c)) Q) :
    RelCT isa P (.seq (.block (a ++ b)) c) Q := by
  have h' := RelCT.assoc' h
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ hp e₁ e₂
  cases e₁ with
  | seq e₁ f₁ =>
    cases e₂ with
    | seq e₂ f₂ => exact h' _ _ _ _ _ _ hp (.seq (splitBlock_exec e₁) f₁) (.seq (splitBlock_exec e₂) f₂)

end VG.Proof.Dsa.AArch64
