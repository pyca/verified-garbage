module

import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Mem

/-!
# A function that chooses, on entry, between two verified functions

`Verified.entryBranch`: a straight-line block `b` that decides a condition
from public data, then a cold branch (`Code.iteCold c c₁ c₂`) to code
verified against `k₁` when it holds and to code verified against `k₂` when
not, is verified against `k`, if from `k`'s precondition the block runs (with
a trace `tr s` the public data determine), leaves `k₁`'s precondition (or
`k₂`'s) and leads from its postcondition, and what `k₁` (or `k₂`) leaves of
the calling convention, to `k`'s; and if two runs with the same public data
take the same branch, from states with the same public data.
-/

@[expose] public section

namespace VG

variable {T : Target}

theorem Exec.block_eq {b : List T.isa.Instr} {s s' : T.isa.State} {t : List Leak}
    (h : Exec T.isa (.block b) s t s') : execBlock T.isa b s = some (s', t) := by
  cases h with
  | block h => exact h

/-- A block of instructions that access no memory leaks nothing. -/
theorem execBlock_trace_nil {M : ISA} {b : List M.Instr} (h : ∀ i ∈ b, ∀ s, M.addrs i s = []) :
    ∀ {s u : M.State} {t : List Leak}, execBlock M b s = some (u, t) → t = [] := by
  induction b with
  | nil => intro s u t e; simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e; exact e.2.symm
  | cons i is ih =>
    intro s u t e
    simp only [execBlock] at e
    split at e
    · cases e
    · rename_i s₁ _
      cases e' : execBlock M is s₁ with
      | none => rw [e'] at e; cases e
      | some p =>
        rw [e'] at e
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        rw [h i List.mem_cons_self s, ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e']
        rfl

theorem Verified.entryBranch {b : List T.isa.Instr} {c : T.isa.Cond} {c₁ c₂ : Prog T.isa}
    {k k₁ k₂ : Contract T.isa} {p : T.isa.State → Bool} (tr : T.isa.State → List Leak)
    (h₁ : Verified T c₁ k₁) (h₂ : Verified T c₂ k₂)
    (hb : ∀ s, k.pre s → ∃ u, execBlock T.isa b s = some (u, tr s) ∧ T.isa.eval c u = some (p s) ∧
      (p s = true → k₁.pre u ∧
        ∀ s', T.abiPreserved u s' → k₁.post u s' → T.abiPreserved s s' ∧ k.post s s') ∧
      (p s = false → k₂.pre u ∧
        ∀ s', T.abiPreserved u s' → k₂.post u s' → T.abiPreserved s s' ∧ k.post s s'))
    (hpub : ∀ s s' u u', k.pre s → k.pre s' → k.pub s s' →
      execBlock T.isa b s = some (u, tr s) → execBlock T.isa b s' = some (u', tr s') →
      tr s = tr s' ∧ p s = p s' ∧ (p s = true → k₁.pub u u') ∧ (p s = false → k₂.pub u u'))
    (hsat : ∃ s, k.pre s) :
    Verified T (.seq (.block b) (Code.iteCold c c₁ c₂)) k := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hq e₁ e₂ => ?_, hsat⟩
  · obtain ⟨u, eb, ec, k1, k2⟩ := hb s hs
    cases hp : p s
    · obtain ⟨hpre, hpost⟩ := k2 hp
      obtain ⟨t, s', e, a, q⟩ := h₂.1 u hpre
      obtain ⟨a', q'⟩ := hpost s' a q
      exact ⟨_, s', .seq (.block eb) (Exec.iteCold_iff.mpr (.iteF (by rw [ec, hp]) e)), a', q'⟩
    · obtain ⟨hpre, hpost⟩ := k1 hp
      obtain ⟨t, s', e, a, q⟩ := h₁.1 u hpre
      obtain ⟨a', q'⟩ := hpost s' a q
      exact ⟨_, s', .seq (.block eb) (Exec.iteCold_iff.mpr (.iteT (by rw [ec, hp]) e)), a', q'⟩
  · obtain ⟨u₁, eb₁, ec₁, k11, k12⟩ := hb s₁ p₁
    obtain ⟨u₂, eb₂, ec₂, k21, k22⟩ := hb s₂ p₂
    cases e₁ with
    | seq a₁ i₁ =>
      cases e₂ with
      | seq a₂ i₂ =>
        have x₁ := Exec.block_eq a₁
        have x₂ := Exec.block_eq a₂
        rw [eb₁] at x₁; rw [eb₂] at x₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj x₁)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj x₂)
        obtain ⟨et, ep, pb1, pb2⟩ := hpub s₁ s₂ _ _ p₁ p₂ hq eb₁ eb₂
        rw [et]
        congr 1
        have i₁ := Exec.iteCold_iff.mp i₁
        have i₂ := Exec.iteCold_iff.mp i₂
        cases hp : p s₁
        · have hp' : p s₂ = false := ep ▸ hp
          cases i₁ with
          | iteT hc _ => rw [ec₁, hp] at hc; cases hc
          | iteF _ r₁ =>
            cases i₂ with
            | iteT hc _ => rw [ec₂, hp'] at hc; cases hc
            | iteF _ r₂ =>
              rw [h₂.2.1 _ _ _ _ _ _ (k12 hp).1 (k22 hp').1 (pb2 hp) r₁ r₂]
        · have hp' : p s₂ = true := ep ▸ hp
          cases i₁ with
          | iteF hc _ => rw [ec₁, hp] at hc; cases hc
          | iteT _ r₁ =>
            cases i₂ with
            | iteF hc _ => rw [ec₂, hp'] at hc; cases hc
            | iteT _ r₂ =>
              rw [h₁.2.1 _ _ _ _ _ _ (k11 hp).1 (k21 hp').1 (pb1 hp) r₁ r₂]

end VG
