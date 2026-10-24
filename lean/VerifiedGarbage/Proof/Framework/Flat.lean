module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Sequences as lists of programs

Structured code nests its sequences in whatever way its definitions build
them, but a relational proof (`RelCT`) may want to cut it anywhere: `flat`
lists the programs of a code in order, splitting every sequence, and
`seqL` runs a list of programs in sequence. A code and its list run the same
and leak the same trace (`exec_flat`), so a proof may run the list instead,
cut where it wants (`exec_seqL_append`).
-/

@[expose] public section

namespace VG

variable {I C : Type}

/-- The programs of `c` in order, every sequence split. -/
def Code.flat : Code I C → List (Code I C)
  | .seq a b => a.flat ++ b.flat
  | c => [c]

/-- The programs of a list in sequence. -/
def Code.seqL : List (Code I C) → Code I C
  | [] => .block []
  | c :: cs => .seq c (Code.seqL cs)

variable {M : ISA}

theorem exec_nil_iff {s s' : M.State} {t : List Leak} :
    Exec M (.block []) s t s' ↔ t = [] ∧ s' = s := by
  constructor
  · intro h
    cases h with
    | block h => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.2.symm, h.1.symm⟩
  · rintro ⟨rfl, rfl⟩; exact .block rfl

theorem exec_seqL_append {l₁ l₂ : List (Prog M)} {s s' : M.State} {t : List Leak} :
    Exec M (Code.seqL (l₁ ++ l₂)) s t s' ↔
      ∃ t₁ t₂ u, t = t₁ ++ t₂ ∧ Exec M (Code.seqL l₁) s t₁ u ∧ Exec M (Code.seqL l₂) u t₂ s' := by
  induction l₁ generalizing s t with
  | nil =>
    simp only [List.nil_append, Code.seqL, exec_nil_iff]
    constructor
    · intro h; exact ⟨[], t, s, rfl, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, _, rfl, ⟨rfl, rfl⟩, h⟩; exact h
  | cons c l ih =>
    simp only [List.cons_append, Code.seqL]
    constructor
    · intro h
      cases h with
      | seq h₁ h₂ =>
        obtain ⟨t₁, t₂, u, rfl, e₁, e₂⟩ := ih.mp h₂
        exact ⟨_, _, u, (List.append_assoc ..).symm, .seq h₁ e₁, e₂⟩
    · rintro ⟨t₁, t₂, u, rfl, e₁, e₂⟩
      cases e₁ with
      | seq h₁ h₂ =>
        rw [List.append_assoc]
        exact .seq h₁ (ih.mpr ⟨_, _, u, rfl, h₂, e₂⟩)

/-- A code and its list run the same and leak the same trace. -/
theorem exec_flat {c : Prog M} {s s' : M.State} {t : List Leak} :
    Exec M c s t s' ↔ Exec M (Code.seqL c.flat) s t s' := by
  induction c generalizing s s' t
  case seq a b iha ihb =>
    simp only [Code.flat]
    rw [exec_seqL_append]
    constructor
    · intro h
      cases h with
      | seq h₁ h₂ => exact ⟨_, _, _, rfl, iha.mp h₁, ihb.mp h₂⟩
    · rintro ⟨t₁, t₂, u, rfl, e₁, e₂⟩
      exact .seq (iha.mpr e₁) (ihb.mpr e₂)
  all_goals
    simp only [Code.flat, Code.seqL]
    constructor
    · intro h; rw [← List.append_nil t]; exact .seq h (.block rfl)
    · intro h
      cases h with
      | seq h₁ h₂ => obtain ⟨rfl, rfl⟩ := exec_nil_iff.mp h₂; rw [List.append_nil]; exact h₁

theorem WP.of_flat {c : Prog M} {l : List (Prog M)} {s : M.State} {Q : M.State → Prop} (hl : c.flat = l)
    (h : WP M c s Q) : WP M (Code.seqL l) s Q :=
  let ⟨t, s', e, hq⟩ := h
  ⟨t, s', hl ▸ exec_flat.mp e, hq⟩

theorem WP.to_flat {c : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (Code.seqL c.flat) s Q) : WP M c s Q :=
  let ⟨t, s', e, hq⟩ := h
  ⟨t, s', exec_flat.mpr e, hq⟩

theorem RelCT.of_flat {P Q : M.State → M.State → Prop} {c : Prog M}
    (h : RelCT M P (Code.seqL c.flat) Q) : RelCT M P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mp e₁) (exec_flat.mp e₂)

/-- Two lists in sequence, related piece by piece. -/
theorem RelCT.seqL_append {P R Q : M.State → M.State → Prop} {l₁ l₂ : List (Prog M)}
    (h₁ : RelCT M P (Code.seqL l₁) R) (h₂ : RelCT M R (Code.seqL l₂) Q) :
    RelCT M P (Code.seqL (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a₁, b₁, u₁, rfl, x₁, y₁⟩ := exec_seqL_append.mp e₁
  obtain ⟨a₂, b₂, u₂, rfl, x₂, y₂⟩ := exec_seqL_append.mp e₂
  obtain ⟨ha, hr⟩ := h₁ _ _ _ _ _ _ hp x₁ x₂
  obtain ⟨hb, hq⟩ := h₂ _ _ _ _ _ _ hr y₁ y₂
  exact ⟨by rw [ha, hb], hq⟩

end VG
