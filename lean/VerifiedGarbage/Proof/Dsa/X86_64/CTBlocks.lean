module
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Timing-preserving composition of adjacent DSA instruction blocks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum.X86_64

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

end VG.Proof.Dsa.X86_64
