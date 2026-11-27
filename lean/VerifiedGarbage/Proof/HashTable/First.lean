module

public import VerifiedGarbage.TCB.Code

/-!
# Variants' functions of the same name have the same code

The tables of every variant of a hash function are coherent (`Coh`): what
two variants call by the same name is the same code. Deciding it compares
the names of every pair of variants and, of every pair of the same name
(each variant with itself at least), their code, instruction by instruction.
`coh_of_first` needs only that each variant's code is that of the first
variant of its name: a comparison of the names before it, and one that the
kernel sees without evaluating the code, as the two name it alike.
-/

@[expose] public section

namespace VG.Proof.HashTable

universe u

/-- Variants `vs` of the same name `k` have the same code `c`, if each has
the code of the first of `vs` with its name, by `kernel_rfl`. -/
theorem coh_of_first {α : Type u} {β : Type} (vs : List α) (k : α → String) (c : α → β)
    (h : vs.map (fun w => some (c w)) = vs.map fun w => (vs.find? fun v => k v == k w).map c) :
    ∀ w ∈ vs, ∀ w' ∈ vs, k w = k w' → c w = c w' := by
  intro w hw w' hw' e
  have h := List.map_inj_left.mp h
  exact Option.some.inj ((h w hw).trans ((by rw [e] : _ = _).trans (h w' hw').symm))

end VG.Proof.HashTable
