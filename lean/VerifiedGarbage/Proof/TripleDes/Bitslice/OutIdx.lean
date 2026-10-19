module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round

/-!
# Which S-box output goes into which word, relative to the written half

`outIdx_off`: the output of S-box `j` into word `x` of the state, written at
the half's offset `wrOff ρ`, is the one into word `x - wrOff ρ` of a state
starting at the left half (`outIdxW`). Every x86-64 bitsliced variant uses it;
it is decided once, here.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Bitslice

open VG.Impl.TripleDes.Bitslice

/-- The output bit of S-box `j` that goes into the left half's word `x`, if any. -/
def outIdxW (j x : Nat) : Option Nat := (List.range 4).find? fun i => lWord (outBit j i) == x

theorem outIdx_off : ∀ ρ : Role, ∀ j < 8, ∀ x < 64, outIdx ρ j x =
    if wrOff ρ ≤ x ∧ x < 63 + wrOff ρ then outIdxW j (x - wrOff ρ) else none := by
  intro ρ; cases ρ <;> lit_decide

end VG.Proof.TripleDes.Bitslice
