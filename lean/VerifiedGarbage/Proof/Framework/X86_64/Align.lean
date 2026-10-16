module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# x86-64: alignment padding

`.block [.align k]` (`Instr.align`, a NOP) runs as the empty block: it leaves
the state as it is and leaks nothing. So code after padding is proven as
without it: `WP.align_seq` for correctness, `RelCT.align_seq` for constant
time.
-/

@[expose] public section

namespace VG.X86_64

theorem execBlock_align {k : Nat} {s : State} :
    execBlock isa ([.align k] : List Instr) s = some (s, []) := (rfl)

theorem Exec.align_iff {k : Nat} {s s' : State} {t : List Leak} :
    Exec isa (.block [.align k]) s t s' ↔ s' = s ∧ t = [] := by
  rw [Exec.block_iff, execBlock_align, Option.some.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

/-- Code after alignment padding, as without it. -/
theorem WP.align_seq {k : Nat} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q) : WP isa (.seq (.block [.align k]) c) s Q :=
  WP.seq ⟨[], s, .block execBlock_align, h⟩

/-- Code after alignment padding, as without it: the padding leaks nothing. -/
theorem RelCT.align_seq {k : Nat} {P Q : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c Q) : RelCT isa P (.seq (.block [.align k]) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.align_iff.mp a₁
      obtain ⟨rfl, rfl⟩ := Exec.align_iff.mp a₂
      exact h _ _ _ _ _ _ hp c₁ c₂

end VG.X86_64
