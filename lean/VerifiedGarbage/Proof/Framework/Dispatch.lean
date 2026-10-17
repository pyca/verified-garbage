module

public import VerifiedGarbage.Impl.Dispatch
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Choosing code by a public selector: proofs

`Dispatch.chain test eq cases` (`Impl/Dispatch.lean`) runs the case whose
key is the selector. For any ISA, given what its tests do (`Tests`: each
`test k` leaks nothing, sets `eq` to whether the selector is `k`, and leaves
a state related to the one before by `R`, with the same selector):

* `chain_wp`: the case of the selector runs, from a state related to the
  one before by `R` (e.g. differing only in a scratch register and the
  flags);
* `chain_exec`: a run of the chain is a run of that case, after the
  branches the tests decide (`trace`), which depend on the selector alone;
* `chain_relCT`: two runs with the same selector are constant time if each
  case is, from states related by `R` to the runs' states before.

The keys are distinct (`Nodup`), and the selector one of them.
-/

@[expose] public section

namespace VG.Proof.Dispatch

open VG.Impl.Dispatch (chain)

variable {M : ISA}

/-- What the tests do: for a key `k` below `B` (what the test's immediate
holds), from any state, `test k` leaks nothing, sets `eq` to whether the
selector `sel` is `k`, and leaves a state related by `R` to the one before,
with the same selector. `R` is reflexive and transitive. -/
structure Tests (test : Nat → List M.Instr) (eq : M.Cond) (sel : M.State → Nat)
    (R : M.State → M.State → Prop) (B : Nat) : Prop where
  step : ∀ k < B, ∀ s, ∃ s', execBlock M (test k) s = some (s', []) ∧
    M.eval eq s' = some (decide (sel s = k)) ∧ R s s' ∧ sel s' = sel s
  refl : ∀ s, R s s
  trans : ∀ {a b c}, R a b → R b c → R a c

/-- The keys of the cases. -/
def keys (cs : List (Nat × Prog M)) : List Nat := cs.map (·.1)

/-- The branches the tests of `chain` decide when the selector is `k`. -/
def trace (k : Nat) : List (Nat × Prog M) → List Leak
  | [] => []
  | [_] => []
  | (k', _) :: c' :: cs => if k = k' then [.branch true] else .branch false :: trace k (c' :: cs)

variable {test : Nat → List M.Instr} {eq : M.Cond} {sel : M.State → Nat}
  {R : M.State → M.State → Prop} {B : Nat}

/-- With distinct keys, one case per key. -/
theorem case_unique {cs : List (Nat × Prog M)} (hnd : (keys cs).Nodup) {k : Nat} {c₁ c₂ : Prog M}
    (h₁ : (k, c₁) ∈ cs) (h₂ : (k, c₂) ∈ cs) : c₁ = c₂ := by
  induction cs with
  | nil => cases h₁
  | cons p cs ih =>
    simp only [keys, List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with e₁ | e₁ <;> rcases List.mem_cons.mp h₂ with e₂ | e₂
    · rw [← e₁] at e₂; cases e₂; rfl
    · subst e₁; exact absurd (List.mem_map.mpr ⟨_, e₂, rfl⟩) hnd.1
    · subst e₂; exact absurd (List.mem_map.mpr ⟨_, e₁, rfl⟩) hnd.1
    · exact ih hnd.2 e₁ e₂

/-- The case of the selector runs, from a state related to the one before by
`R`, with the same selector. -/
theorem chain_wp (T : Tests test eq sel R B) :
    ∀ (cs : List (Nat × Prog M)) {s : M.State} {Q : M.State → Prop}, (∀ k ∈ keys cs, k < B) →
      sel s ∈ keys cs → (keys cs).Nodup →
      (∀ c, (sel s, c) ∈ cs → ∀ s', R s s' → sel s' = sel s → WP M c s' Q) →
      WP M (chain test eq cs) s Q
  | [], _, _, _, hk, _, _ => absurd hk (by simp [keys])
  | [(k, c)], s, _, _, hk, _, h => by
    simp only [keys, List.map_cons, List.map_nil, List.mem_singleton] at hk
    exact h c (by rw [hk]; exact List.mem_singleton_self _) s (T.refl s) rfl
  | (k, c) :: c' :: cs, s, Q, hB, hk, hnd, h => by
    obtain ⟨s', hb, hc, hr, hs⟩ := T.step k (hB k List.mem_cons_self) s
    refine WP.seq ⟨[], s', .block hb, ?_⟩
    refine WP.ite _ hc (fun ht => ?_) (fun hf => ?_)
    · rw [decide_eq_true_eq] at ht
      exact h c (by rw [ht]; exact List.mem_cons_self) s' hr hs
    · rw [decide_eq_false_iff_not] at hf
      have hk' : sel s ∈ keys (c' :: cs) := by
        simp only [keys, List.map_cons, List.mem_cons] at hk ⊢; exact hk.resolve_left hf
      have hnd' : (keys (c' :: cs)).Nodup := by
        simp only [keys, List.map_cons, List.nodup_cons] at hnd ⊢; exact hnd.2
      refine chain_wp T (c' :: cs) (fun k' hk'' => hB k' (List.mem_cons_of_mem _ hk''))
        (by rw [hs]; exact hk') hnd' fun c₁ hc₁ s₁ hr₁ hs₁ => ?_
      rw [hs] at hc₁
      exact h c₁ (List.mem_cons_of_mem _ hc₁) s₁ (T.trans hr hr₁) (hs₁.trans hs)

/-- A run of the chain is a run of the selector's case, from a state related
by `R` to the one before with the same selector, after the branches of the
tests (`trace`). -/
theorem chain_exec (T : Tests test eq sel R B) :
    ∀ (cs : List (Nat × Prog M)) {s s' : M.State} {t : List Leak}, (∀ k ∈ keys cs, k < B) →
      sel s ∈ keys cs → Exec M (chain test eq cs) s t s' →
      ∃ c s₀ t₀, (sel s, c) ∈ cs ∧ R s s₀ ∧ sel s₀ = sel s ∧ Exec M c s₀ t₀ s' ∧
        t = trace (sel s) cs ++ t₀
  | [], _, _, _, _, hk, _ => absurd hk (by simp [keys])
  | [(k, c)], s, _, t, _, hk, he => by
    simp only [keys, List.map_cons, List.map_nil, List.mem_singleton] at hk
    exact ⟨c, s, t, by rw [hk]; exact List.mem_singleton_self _, T.refl s, rfl, he, rfl⟩
  | (k, c) :: c' :: cs, s, s', t, hB, hk, he => by
    obtain ⟨s₁, hb, hc, hr, hs⟩ := T.step k (hB k List.mem_cons_self) s
    cases he with
    | seq e₁ e₂ =>
      rw [Exec.block_iff, hb] at e₁
      cases e₁
      cases e₂ with
      | iteT hc' e =>
        rw [hc] at hc'
        have ht : sel s = k := of_decide_eq_true (Option.some.inj hc')
        refine ⟨c, s₁, _, by rw [ht]; exact List.mem_cons_self, hr, hs, e, ?_⟩
        simp only [trace, ht, ite_true, List.nil_append, List.singleton_append]
      | iteF hc' e =>
        rw [hc] at hc'
        have hf : sel s ≠ k := of_decide_eq_false (Option.some.inj hc')
        have hk' : sel s ∈ keys (c' :: cs) := by
          simp only [keys, List.map_cons, List.mem_cons] at hk ⊢; exact hk.resolve_left hf
        obtain ⟨c₁, s₀, t₀, hm, hr₀, hs₀, e₀, rfl⟩ := chain_exec T (c' :: cs)
          (fun k' hk'' => hB k' (List.mem_cons_of_mem _ hk'')) (by rw [hs]; exact hk') e
        rw [hs] at hm hs₀
        refine ⟨c₁, s₀, t₀, List.mem_cons_of_mem _ hm, T.trans hr hr₀, hs₀, e₀, ?_⟩
        simp only [trace, hf, ite_false, hs, List.nil_append, List.cons_append]

/-- Two runs with the same selector, one of the keys, are constant time if
each case is, from states related by `R` to the states before (whose
relation `P` they keep), with that selector. -/
theorem chain_relCT (T : Tests test eq sel R B) {cs : List (Nat × Prog M)} (hB : ∀ k ∈ keys cs, k < B)
    (hnd : (keys cs).Nodup)
    {P Q : M.State → M.State → Prop}
    (hs : ∀ s₁ s₂, P s₁ s₂ → sel s₁ = sel s₂ ∧ sel s₁ ∈ keys cs)
    (h : ∀ k c, (k, c) ∈ cs → RelCT M (fun s₁ s₂ => ∃ a₁ a₂, P a₁ a₂ ∧ sel a₁ = k ∧
      R a₁ s₁ ∧ R a₂ s₂ ∧ sel s₁ = k ∧ sel s₂ = k) c Q) :
    RelCT M P (chain test eq cs) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨he, hk⟩ := hs _ _ hp
  obtain ⟨c₁, a₁, u₁, m₁, r₁, q₁, x₁, rfl⟩ := chain_exec T cs hB hk e₁
  obtain ⟨c₂, a₂, u₂, m₂, r₂, q₂, x₂, rfl⟩ := chain_exec T cs hB (he ▸ hk) e₂
  rw [← he] at m₂ q₂ ⊢
  rw [case_unique hnd m₂ m₁] at x₂
  obtain ⟨rfl, hq⟩ := h _ _ m₁ _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, r₁, r₂, q₁, q₂⟩ x₁ x₂
  exact ⟨rfl, hq⟩

end VG.Proof.Dispatch
