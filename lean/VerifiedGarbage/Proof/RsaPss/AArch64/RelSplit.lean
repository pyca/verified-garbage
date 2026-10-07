import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Splitting the first block of a sequence

`RelCT.seq_block_append`: a sequence whose first block is `l₁ ++ l₂` runs as
`l₁` followed by `l₂` and the rest, and leaks the same trace, so a relational
proof may relate `l₁` alone (e.g. a load of a value public by correctness)
and check `l₂` with the rest by the taint analysis.
-/

namespace VG

variable {M : ISA}

theorem RelCT.seq_block_append {P Q : M.State → M.State → Prop} {l₁ l₂ : List M.Instr} {c : Prog M}
    (h : RelCT M P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT M P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨x₁, u₁⟩, hx₁, hy₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨y₁, w₁⟩, hz₁, he₁⟩ := Option.map_eq_some_iff.mp hy₁
      obtain ⟨⟨x₂, u₂⟩, hx₂, hy₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨y₂, w₂⟩, hz₂, he₂⟩ := Option.map_eq_some_iff.mp hy₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block hx₁) (.seq (.block hz₁) c₁))
        (.seq (.block hx₂) (.seq (.block hz₂) c₂))
      simp only [List.append_assoc]
      exact ⟨ht, hq⟩

end VG
