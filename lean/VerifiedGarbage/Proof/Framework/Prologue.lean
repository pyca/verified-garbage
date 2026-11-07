module

public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Code after a prologue

`Verified.of_prologue`: code `c` verified against a contract `k` is verified
against another contract `k'` when it runs after a block `b` that leaks
nothing and takes every state `k'` allows to one `k` allows (e.g. a function
whose arguments are those of `c` but one, which `b` moves into the registers
`c` takes them in, and sets the one left out to a constant). What the
target's calling convention preserves across `c` it must preserve across `b`
too (`habi`), and `k`'s postcondition and public data, read on the state
after `b`, must give `k'`'s.
-/

@[expose] public section

namespace VG

theorem Verified.of_prologue {T : Target} {b : List T.isa.Instr} {c : Prog T.isa}
    {k k' : Contract T.isa} (hv : Verified T c k) (f : T.isa.State → T.isa.State)
    (hrun : ∀ s, k'.pre s → execBlock T.isa b s = some (f s, []))
    (hpre : ∀ s, k'.pre s → k.pre (f s))
    (habi : ∀ s s', k'.pre s → T.abiPreserved (f s) s' → T.abiPreserved s s')
    (hpost : ∀ s s', k'.pre s → k.post (f s) s' → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub (f s₁) (f s₂))
    (hsat : ∃ s, k'.pre s) :
    Verified T (.seq (.block b) c) k' := by
  obtain ⟨hc, hct, -⟩ := hv
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc (f s) (hpre s hs)
    exact ⟨[] ++ t, s', .seq (.block (hrun s hs)) he, habi s s' hs ha, hpost s s' hs hq⟩
  · cases e₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq b₂ c₂ =>
        cases b₁ with
        | block r₁ =>
          cases b₂ with
          | block r₂ =>
            rw [hrun _ h₁] at r₁
            rw [hrun _ h₂] at r₂
            cases r₁; cases r₂
            exact congrArg ([] ++ ·)
              (hct _ _ _ _ _ _ (hpre _ h₁) (hpre _ h₂) (hpub _ _ h₁ h₂ hp) c₁ c₂)

end VG
