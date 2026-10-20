module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Block

/-!
# A prefix of a sequence, in relational constant-time proofs

Structured code nests its sequences to the right, `a₁; (a₂; (…; rest))`
(`Prog.chain [a₁, a₂, …] rest`). A relational proof that checks every piece
before `rest` with the taint analysis at once, and relates `rest` otherwise,
splits it as `(a₁; (a₂; (…; skip))); rest` (`RelCT.chain`): the prefix ends
in an empty block, so a correctness lemma about `a₁; (a₂; (…; P))` for any
`P` gives the prefix's postcondition.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- `a₁; (a₂; (…; rest))`. -/
def Prog.chain : List (Prog M) → Prog M → Prog M
  | [], r => r
  | a :: l, r => .seq a (Prog.chain l r)

theorem Exec.of_chain {l : List (Prog M)} {rest : Prog M} {s s' : M.State} {t : List Leak}
    (e : Exec M (Prog.chain l rest) s t s') : Exec M (.seq (Prog.chain l (.block [])) rest) s t s' := by
  induction l generalizing s t with
  | nil =>
    have z : Exec M (.block []) s [] s := .block (by simp [execBlock])
    show Exec M (.seq (.block []) rest) s t s'
    exact List.nil_append t ▸ Exec.seq z e
  | cons a l ih =>
    cases e with
    | seq e₁ e₂ =>
      cases ih e₂ with
      | seq e₃ e₄ =>
        show Exec M (.seq (.seq a (Prog.chain l (.block []))) rest) s _ s'
        rw [← List.append_assoc]
        exact Exec.seq (Exec.seq e₁ e₃) e₄

theorem RelCT.chain {P Q : M.State → M.State → Prop} {l : List (Prog M)} {rest : Prog M}
    (h : RelCT M P (.seq (Prog.chain l (.block [])) rest) Q) : RelCT M P (Prog.chain l rest) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp e₁.of_chain e₂.of_chain

end VG
