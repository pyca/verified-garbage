module

/-!
# `omega`'s decisions without Mathlib's instance search

Untrusted: this only changes how proofs are found.

`omega` decides facts about the coefficients of its constraints, among them
`Coeffs.isZero xs` (`∀ x, x ∈ xs → x = 0`), and synthesizes their
`Decidable` instances. With Mathlib imported, the search for this one tries
Mathlib's instances for bounded quantifiers (over finite sets, finite types,
…) before core's, about a hundredth of a second for each call of `omega`:
a tenth of the time of proofs that call it hundreds of times. This instance,
tried first, is the one the search finds (`List.decidableBAll`, deciding each
`x = 0` by `Int.instDecidableEq`).
-/

@[expose] public section


namespace VG

instance (priority := high) instDecidableCoeffsIsZero (xs : Lean.Omega.Coeffs) :
    Decidable xs.isZero :=
  @List.decidableBAll _ (fun x => x = 0) (fun x => Int.instDecidableEq x 0) xs

end VG
