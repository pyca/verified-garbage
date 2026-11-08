module

public import VerifiedGarbage.Impl.BrainpoolP384r1.CombTable7

/-!
# brainpoolP384r1: the shape of the 7-bit comb's tables

`comb7` has 55 tables of 64 points: what `tcombWords_length` needs to count
the words of the tables in memory. Proven once here, with no target, as
`Proof/P384/Comb7Shape.lean`.
-/

-- separate module: the tables' shape, which the kernel checks by walking every table, is target-independent, so other targets' combs can share it

@[expose] public section

namespace VG.Proof.BrainpoolP384r1

open VG.Impl.BrainpoolP384r1 (comb7)

theorem comb7_length : comb7.length = 55 := by decide +kernel

/-- Every table has 64 points (checked by `List.all`, which walks the tables
once, rather than by `getD` at each index). -/
theorem comb7_rows : ∀ j < 55, (comb7.getD j []).length = 64 := by
  have h := List.all_eq_true.mp (show comb7.all (·.length == 64) = true by decide +kernel)
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (comb7_length ▸ hj), Option.getD_some]
  exact beq_iff_eq.mp (h _ (List.getElem_mem _))

end VG.Proof.BrainpoolP384r1
