module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Relating two runs instruction by instruction

`RelCT.of_steps`: code made only of blocks, sequences, branches and loops
(`Code.plainAll`, no calls or frames), each of whose instructions keeps a
relation `R` between two runs and accesses the same addresses in both, and
whose every branch condition agrees in both runs under `R`, keeps `R` and
leaks the same trace. A residue proof (`TCB/<ISA>/Residue.lean`) uses it with
`R` the relation of two runs that agree outside the buffers, for code whose
instructions never read memory: what such code leaves is then a function of
what agrees.
-/

@[expose] public section

namespace VG

/-- `c` is made of blocks, sequences, branches and loops only, and each of
its instructions satisfies `p`. -/
def Code.plainAll {I C : Type} (p : I → Bool) : Code I C → Bool
  | .block is => is.all p
  | .seq a b => a.plainAll p && b.plainAll p
  | .ite _ t e => t.plainAll p && e.plainAll p
  | .loop b _ => b.plainAll p
  | _ => false

variable {M : ISA}

/-- A block each of whose instructions satisfies `p`, which keeps `R` and
accesses the same addresses in both runs, keeps `R` and leaks the same
trace. -/
theorem execBlock_rel {R : M.State → M.State → Prop} {p : M.Instr → Bool}
    (hstep : ∀ i, p i = true → ∀ s₁ s₂ a b, R s₁ s₂ → M.exec i s₁ = some a →
      M.exec i s₂ = some b → R a b ∧ M.addrs i s₁ = M.addrs i s₂) :
    ∀ (is : List M.Instr), is.all p = true → ∀ s₁ s₂ s₁' s₂' t₁ t₂, R s₁ s₂ →
      execBlock M is s₁ = some (s₁', t₁) → execBlock M is s₂ = some (s₂', t₂) →
      R s₁' s₂' ∧ t₁ = t₂
  | [], _, s₁, s₂, s₁', s₂', t₁, t₂, hr, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨hr, rfl⟩
  | i :: is, hp, s₁, s₂, s₁', s₂', t₁, t₂, hr, h₁, h₂ => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    simp only [execBlock] at h₁ h₂
    cases e₁ : M.exec i s₁ with
    | none => rw [e₁] at h₁; cases h₁
    | some a =>
      cases e₂ : M.exec i s₂ with
      | none => rw [e₂] at h₂; cases h₂
      | some b =>
        rw [e₁] at h₁
        rw [e₂] at h₂
        obtain ⟨hab, had⟩ := hstep i hp.1 _ _ _ _ hr e₁ e₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hq, ht⟩ := execBlock_rel hstep is hp.2 _ _ p₁.1 p₂.1 p₁.2 p₂.2 hab
          (by rw [hp₁]) (by rw [hp₂])
        exact ⟨hq, by rw [had, ht]⟩

/-- Plain code (`Code.plainAll p`) whose instructions keep `R` and access
the same addresses in both runs, and whose conditions agree under `R`, keeps
`R` and leaks the same trace. -/
theorem RelCT.of_steps {R : M.State → M.State → Prop} {p : M.Instr → Bool}
    (hstep : ∀ i, p i = true → ∀ s₁ s₂ a b, R s₁ s₂ → M.exec i s₁ = some a →
      M.exec i s₂ = some b → R a b ∧ M.addrs i s₁ = M.addrs i s₂)
    (hcond : ∀ c s₁ s₂, R s₁ s₂ → M.eval c s₁ = M.eval c s₂) :
    ∀ {c : Prog M}, c.plainAll p = true → RelCT M R c R := by
  intro c hc s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  induction e₁ generalizing s₂ t₂ s₂' with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      obtain ⟨hq, ht⟩ := execBlock_rel hstep _ hc _ _ _ _ _ _ hr h₁ h₂
      exact ⟨ht, hq⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.plainAll, Bool.and_eq_true] at hc
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, hm⟩ := ih₁ hc.1 _ _ _ hr a₂
      obtain ⟨rfl, hq⟩ := ih₂ hc.2 _ _ _ hm b₂
      exact ⟨rfl, hq⟩
  | iteT c₁ _ ih =>
    simp only [Code.plainAll, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ a₂ => obtain ⟨rfl, hq⟩ := ih hc.1 _ _ _ hr a₂; exact ⟨rfl, hq⟩
    | iteF c₂ _ => rw [hcond _ _ _ hr, c₂] at c₁; cases c₁
  | iteF c₁ _ ih =>
    simp only [Code.plainAll, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT c₂ _ => rw [hcond _ _ _ hr, c₂] at c₁; cases c₁
    | iteF _ a₂ => obtain ⟨rfl, hq⟩ := ih hc.2 _ _ _ hr a₂; exact ⟨rfl, hq⟩
  | loopExit _ c₁ ih =>
    cases e₂ with
    | loopExit b₂ _ => obtain ⟨rfl, hq⟩ := ih hc _ _ _ hr b₂; exact ⟨rfl, hq⟩
    | loopNext b₂ c₂ _ =>
      obtain ⟨-, hq⟩ := ih hc _ _ _ hr b₂
      rw [hcond _ _ _ hq, c₂] at c₁; cases c₁
  | loopNext _ c₁ _ ih₁ ih₂ =>
    cases e₂ with
    | loopExit b₂ c₂ =>
      obtain ⟨-, hq⟩ := ih₁ hc _ _ _ hr b₂
      rw [hcond _ _ _ hq, c₂] at c₁; cases c₁
    | loopNext b₂ _ r₂ =>
      obtain ⟨rfl, hq⟩ := ih₁ hc _ _ _ hr b₂
      obtain ⟨rfl, hq'⟩ := ih₂ hc _ _ _ hq r₂
      exact ⟨rfl, hq'⟩
  | call => simp [Code.plainAll] at hc
  | frame => simp [Code.plainAll] at hc
  | icall => simp [Code.plainAll] at hc
  | icallNext => simp [Code.plainAll] at hc

end VG
