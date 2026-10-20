module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Two runs from two given states leak the same trace

`SameTrace M c s₁ s₂`: any runs of `c` from `s₁` and from `s₂` leak the same
trace. It composes as a weakest precondition does (`SameTrace.seq`): what
each run satisfies after the first part, by its correctness, is what the
second part's runs start from. A part whose trace a taint analysis shows
public (`RelCT` from agreeing states) is a leaf (`SameTrace.of_relCT`).
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- Any runs of `c` from `s₁` and from `s₂` leak the same trace. -/
def SameTrace (M : ISA) (c : Prog M) (s₁ s₂ : M.State) : Prop :=
  ∀ tr₁ tr₂ t₁ t₂, Exec M c s₁ tr₁ t₁ → Exec M c s₂ tr₂ t₂ → tr₁ = tr₂

namespace SameTrace

theorem of_relCT {P Q : M.State → M.State → Prop} {c : Prog M} {s₁ s₂ : M.State} (h : RelCT M P c Q)
    (hp : P s₁ s₂) : SameTrace M c s₁ s₂ :=
  fun _ _ _ _ e₁ e₂ => (h _ _ _ _ _ _ hp e₁ e₂).1

theorem to_relCT {c : Prog M} {s₁ s₂ : M.State} (h : SameTrace M c s₁ s₂) :
    RelCT M (fun a b => a = s₁ ∧ b = s₂) c (fun _ _ => True) := by
  rintro _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨h _ _ _ _ e₁ e₂, trivial⟩

theorem seq {c d : Prog M} {s₁ s₂ : M.State} {F₁ F₂ : M.State → Prop} (h : SameTrace M c s₁ s₂)
    (W₁ : WP M c s₁ F₁) (W₂ : WP M c s₂ F₂) (k : ∀ t₁ t₂, F₁ t₁ → F₂ t₂ → SameTrace M d t₁ t₂) :
    SameTrace M (.seq c d) s₁ s₂ := by
  intro tr₁ tr₂ t₁ t₂ e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨_, u₁, f₁, g₁⟩ := W₁
      obtain ⟨_, u₂, f₂, g₂⟩ := W₂
      obtain ⟨-, rfl⟩ := Exec.det a₁ f₁
      obtain ⟨-, rfl⟩ := Exec.det a₂ f₂
      rw [h _ _ _ _ a₁ a₂, k _ _ g₁ g₂ _ _ _ _ b₁ b₂]

theorem ite {c : M.Cond} {th el : Prog M} {s₁ s₂ : M.State} (hc : M.eval c s₁ = M.eval c s₂)
    (ht : M.eval c s₁ = some true → SameTrace M th s₁ s₂) (he : M.eval c s₁ = some false → SameTrace M el s₁ s₂) :
    SameTrace M (.ite c th el) s₁ s₂ := by
  intro tr₁ tr₂ t₁ t₂ e₁ e₂
  cases e₁ with
  | iteT c₁ a₁ =>
    cases e₂ with
    | iteT _ a₂ => rw [ht c₁ _ _ _ _ a₁ a₂]
    | iteF c₂ _ => rw [hc, c₂] at c₁; cases c₁
  | iteF c₁ a₁ =>
    cases e₂ with
    | iteT c₂ _ => rw [hc, c₂] at c₁; cases c₁
    | iteF _ a₂ => rw [he c₁ _ _ _ _ a₁ a₂]

theorem block_nil {s₁ s₂ : M.State} : SameTrace M (.block []) s₁ s₂ := by
  intro tr₁ tr₂ t₁ t₂ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      rw [← h₁.2, ← h₂.2]

theorem block_append {l₁ l₂ : List M.Instr} {s₁ s₂ : M.State}
    (h : SameTrace M (.seq (.block l₁) (.block l₂)) s₁ s₂) : SameTrace M (.block (l₁ ++ l₂)) s₁ s₂ :=
  of_relCT (RelCT.block_append h.to_relCT) ⟨rfl, rfl⟩

theorem assoc {a b c : Prog M} {s₁ s₂ : M.State} (h : SameTrace M (.seq (.seq a b) c) s₁ s₂) :
    SameTrace M (.seq a (.seq b c)) s₁ s₂ :=
  of_relCT (RelCT.assoc h.to_relCT) ⟨rfl, rfl⟩

theorem assoc_left {a b c : Prog M} {s₁ s₂ : M.State} (h : SameTrace M (.seq a (.seq b c)) s₁ s₂) :
    SameTrace M (.seq (.seq a b) c) s₁ s₂ := by
  intro tr₁ tr₂ t₁ t₂ e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          have H := h _ _ _ _ (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simpa only [List.append_assoc] using H

theorem nil_seq {c : Prog M} {s₁ s₂ : M.State} (h : SameTrace M c s₁ s₂) :
    SameTrace M (.seq (.block []) c) s₁ s₂ :=
  seq block_nil (WP.block_nil (Q := fun t => t = s₁) rfl) (WP.block_nil (Q := fun t => t = s₂) rfl)
    fun _ _ e₁ e₂ => e₁ ▸ e₂ ▸ h

/-- A branch followed by code: each branch followed by it. -/
theorem seq_ite {c : M.Cond} {th el r : Prog M} {s₁ s₂ : M.State} (hc : M.eval c s₁ = M.eval c s₂)
    (ht : M.eval c s₁ = some true → SameTrace M (.seq th r) s₁ s₂)
    (he : M.eval c s₁ = some false → SameTrace M (.seq el r) s₁ s₂) :
    SameTrace M (.seq (.ite c th el) r) s₁ s₂ := by
  intro tr₁ tr₂ t₁ t₂ e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases a₁ with
      | iteT c₁ x₁ =>
        cases a₂ with
        | iteT _ x₂ =>
          have H := ht c₁ _ _ _ _ (.seq x₁ b₁) (.seq x₂ b₂)
          simp only [List.cons_append, H]
        | iteF c₂ _ => rw [hc, c₂] at c₁; cases c₁
      | iteF c₁ x₁ =>
        cases a₂ with
        | iteT c₂ _ => rw [hc, c₂] at c₁; cases c₁
        | iteF _ x₂ =>
          have H := he c₁ _ _ _ _ (.seq x₁ b₁) (.seq x₂ b₂)
          simp only [List.cons_append, H]

theorem constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (h : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → SameTrace M c s₁ s₂) : ConstantTime M Pre Pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => h _ _ h₁ h₂ hp _ _ _ _ e₁ e₂

end SameTrace

end VG
