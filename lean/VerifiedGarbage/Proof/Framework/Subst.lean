module

import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Subst
public import VerifiedGarbage.TCB.Artifact

/-!
# Replacing a piece of code by one that simulates it

`Code.subst a b c` is `c` with every occurrence of the code `a` replaced by
`b`. If every run of `a` is also a run of `b`, with the same trace and the
same final state (`Sim a b`), every run of `c` is a run of `Code.subst a b c`
(`Exec.subst`), and a `Verified` proof of `c` is one of `Code.subst a b c`
(`Verified.subst`): the semantics is deterministic, so the runs of
`Code.subst a b c` from the states the contract allows are those of `c`.
-/

@[expose] public section

namespace VG

variable {M : ISA} [DecidableEq M.Instr] [DecidableEq M.Cond]

/-- Every run of `a` is a run of `b`, with the same trace and final state. -/
def Sim (a b : Prog M) : Prop := ∀ {s t s'}, Exec M a s t s' → Exec M b s t s'

theorem Exec.subst {a b : Prog M} (hab : Sim a b) {c : Prog M} {s s' : M.State} {t : List Leak}
    (h : Exec M c s t s') : Exec M (Code.subst a b c) s t s' := by
  induction h with
  | block h =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .block h)
    · exact .block h
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .seq h₁ h₂)
    · exact .seq ih₁ ih₂
  | iteT hc h ih =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .iteT hc h)
    · exact .iteT hc ih
  | iteF hc h ih =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .iteF hc h)
    · exact .iteF hc ih
  | loopExit h hc ih =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .loopExit h hc)
    · exact .loopExit ih hc
  | loopNext h hc h' ih ih' =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .loopNext h hc h')
    · rename_i e
      simp only [Code.subst, e, ↓reduceIte] at ih'
      exact .loopNext ih hc ih'
  | call hc h hr ih =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .call hc h hr)
    · exact .call hc ih hr
  | frame hp h hq ih =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .frame hp h hq)
    · exact .frame hp ih hq
  | icall hi hc h hr _ =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .icall hi hc h hr)
    · exact .icall hi hc h hr
  | icallNext hi hne h _ =>
    simp only [Code.subst]; split
    · rename_i e; exact hab (e ▸ .icallNext hi hne h)
    · exact .icallNext hi hne h

/-- A `Verified` proof carries over to code whose runs include every run of
the proven code. -/
theorem Verified.of_sim {T : Target} {c c' : Prog T.isa} {k : Contract T.isa} (h : Verified T c k)
    (sim : ∀ {s t s'}, Exec T.isa c s t s' → Exec T.isa c' s t s') : Verified T c' k := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂ => ?_, h.2.2⟩
  · obtain ⟨t, s', e, ha, hq⟩ := h.1 s hs
    exact ⟨t, s', sim e, ha, hq⟩
  · obtain ⟨u₁, o₁, f₁, -⟩ := h.1 s₁ p₁
    obtain ⟨u₂, o₂, f₂, -⟩ := h.1 s₂ p₂
    rw [← (Exec.det (sim f₁) e₁).1, ← (Exec.det (sim f₂) e₂).1]
    exact h.2.1 s₁ s₂ u₁ u₂ o₁ o₂ p₁ p₂ hp f₁ f₂

theorem Verified.subst {T : Target} [DecidableEq T.isa.Instr] [DecidableEq T.isa.Cond]
    {a b c : Prog T.isa} {k : Contract T.isa} (h : Verified T c k) (hab : Sim a b) :
    Verified T (Code.subst a b c) k :=
  h.of_sim (Exec.subst hab)

end VG
