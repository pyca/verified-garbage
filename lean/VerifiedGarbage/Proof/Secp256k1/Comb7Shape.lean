module

public import VerifiedGarbage.Impl.Secp256k1.CombTable7

/-!
# secp256k1: the shape of the 7-bit comb's tables

`secp256k1Comb7` has 37 tables of 64 points: what `tcombWords_length` needs to count
the words of the tables in memory, on every target. Proven once here, with no
target: the kernel walks every table (a second for P-521's), which each
target's proof would otherwise repeat.
-/

@[expose] public section

namespace VG.Proof.Secp256k1

open VG.Impl.Secp256k1 (secp256k1Comb7)

theorem secp256k1Comb7_length : secp256k1Comb7.length = 37 := by decide +kernel

/-- Every table has 64 points (checked by `List.all`, which walks the tables
once, rather than by `getD` at each index). -/
theorem secp256k1Comb7_rows : ∀ j < 37, (secp256k1Comb7.getD j []).length = 64 := by
  have h := List.all_eq_true.mp (show secp256k1Comb7.all (·.length == 64) = true by decide +kernel)
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (secp256k1Comb7_length ▸ hj), Option.getD_some]
  exact beq_iff_eq.mp (h _ (List.getElem_mem _))

end VG.Proof.Secp256k1
