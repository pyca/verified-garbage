module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Code after a branch moved into both arms, the arms swapped

`ite c' (b; k) (a; k)`, with `c'` the negation of `c`, runs as
`(ite c a b); k`: the same final state, its trace with the branch's
outcome negated. Only the layout differs: the printer lays out an `ite`'s
`else` arm where the code before it falls through (`Printer.lower`), so the
arm `a` and the code `k` after it then run without a jump. This moves
correctness (`Exec.ite_seq_swap_of`) and relational constant time
(`RelCT.ite_seq_swap`) from the one to the other: two runs whose negated
outcomes agree have agreeing outcomes.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- A run of `ite c' (b; k) (a; k)` is one of `(ite c a b); k`, with the
branch's outcome negated in its trace. -/
theorem Exec.ite_seq_swap {c c' : M.Cond} {a b k : Prog M}
    (hc : ∀ s, M.eval c' s = (M.eval c s).map (!·)) {s s' : M.State} {t : List Leak}
    (h : Exec M (.ite c' (.seq b k) (.seq a k)) s t s') :
    ∃ x u, t = .branch x :: u ∧ Exec M (.seq (.ite c a b) k) s (.branch (!x) :: u) s' := by
  cases h with
  | iteT h₁ h₂ =>
    cases h₂ with
    | seq eb ek =>
      have hf : M.eval c s = some false := by
        rw [hc] at h₁
        cases e : M.eval c s with
        | none => rw [e] at h₁; cases h₁
        | some y => rw [e] at h₁; cases y <;> simp_all
      exact ⟨true, _, rfl, by simpa using Exec.seq (Exec.iteF hf eb) ek⟩
  | iteF h₁ h₂ =>
    cases h₂ with
    | seq ea ek =>
      have ht : M.eval c s = some true := by
        rw [hc] at h₁
        cases e : M.eval c s with
        | none => rw [e] at h₁; cases h₁
        | some y => rw [e] at h₁; cases y <;> simp_all
      exact ⟨false, _, rfl, by simpa using Exec.seq (Exec.iteT ht ea) ek⟩

/-- A run of `(ite c a b); k` gives one of `ite c' (b; k) (a; k)`. -/
theorem Exec.ite_seq_swap_of {c c' : M.Cond} {a b k : Prog M}
    (hc : ∀ s, M.eval c' s = (M.eval c s).map (!·)) {s s' : M.State} {t : List Leak}
    (h : Exec M (.seq (.ite c a b) k) s t s') : ∃ t', Exec M (.ite c' (.seq b k) (.seq a k)) s t' s' := by
  cases h with
  | seq h₁ ek =>
    cases h₁ with
    | iteT ht ea => exact ⟨_, Exec.iteF (by rw [hc, ht]; rfl) (Exec.seq ea ek)⟩
    | iteF hf eb => exact ⟨_, Exec.iteT (by rw [hc, hf]; rfl) (Exec.seq eb ek)⟩

/-- A run of `p; X` gives one of `p; X'` if each run of `X` gives one of `X'`. -/
theorem Exec.seq_right_of {p X X' : Prog M}
    (hX : ∀ {s t s'}, Exec M X s t s' → ∃ t', Exec M X' s t' s') {s s' : M.State} {t : List Leak}
    (h : Exec M (.seq p X) s t s') : ∃ t', Exec M (.seq p X') s t' s' := by
  cases h with
  | seq ep eX =>
    obtain ⟨_, e⟩ := hX eX
    exact ⟨_, Exec.seq ep e⟩

theorem RelCT.ite_seq_swap {P Q : M.State → M.State → Prop} {c c' : M.Cond} {a b k : Prog M}
    (hc : ∀ s, M.eval c' s = (M.eval c s).map (!·)) (h : RelCT M P (.seq (.ite c a b) k) Q) :
    RelCT M P (.ite c' (.seq b k) (.seq a k)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨x₁, u₁, rfl, o₁⟩ := Exec.ite_seq_swap hc e₁
  obtain ⟨x₂, u₂, rfl, o₂⟩ := Exec.ite_seq_swap hc e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp o₁ o₂
  simp only [List.cons.injEq, Leak.branch.injEq, Bool.not_inj_iff] at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨rfl, hq⟩

end VG
