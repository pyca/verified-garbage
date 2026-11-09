module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Dsa.Generation.Chunks

/-! # How many `h` candidates the generator search reads

`generator` finds `g` in a list of `h` candidates; `generatorCount` is how
many of them it reads: up to and including the one giving `g`, or all of
them. The refillable-tape search (`Spec/Dsa/ParameterSearch.lean`) consumes
that many candidates' octets. -/

@[expose] public section

namespace VG.Proof.Dsa.Generation

/-- Whether the candidate `h` gives a generator of the order-`q` subgroup
mod `p` (A.2.1). -/
def generatorHit (p q h : Nat) : Bool :=
  (1 < h && h < p - 1) && 1 < Spec.Dsa.powMod h ((p - 1) / q) p

/-- The `h` candidates `generator p q` reads. -/
def generatorCount (p q : Nat) : List Nat → Nat
  | [] => 0
  | h :: hs => if generatorHit p q h then 1 else generatorCount p q hs + 1

theorem generatorCount_le (p q : Nat) (hs : List Nat) : generatorCount p q hs ≤ hs.length := by
  induction hs with
  | nil => simp [generatorCount]
  | cons h hs ih => simp only [generatorCount, List.length_cons]; split <;> omega

/-- No complete chunk left: no candidate is read. -/
theorem generatorCount_chunks_done {width p q : Nat} {bytes : List Byte}
    (h : bytes.length < width) :
    generatorCount p q ((Spec.Dsa.generationChunks width bytes).map Spec.Dsa.decodeBE) = 0 := by
  rw [generationChunks_done h]; rfl

/-- The first complete chunk is read; the search stops there if it gives `g`. -/
theorem generatorCount_chunks_step {width p q : Nat} {bytes : List Byte}
    (hw : 0 < width) (h : width ≤ bytes.length) :
    generatorCount p q ((Spec.Dsa.generationChunks width bytes).map Spec.Dsa.decodeBE) =
      if 1 < Spec.Dsa.decodeBE (bytes.take width) ∧ Spec.Dsa.decodeBE (bytes.take width) < p - 1 ∧
          1 < Spec.Dsa.powMod (Spec.Dsa.decodeBE (bytes.take width)) ((p - 1) / q) p then 1
      else generatorCount p q
        ((Spec.Dsa.generationChunks width (bytes.drop width)).map Spec.Dsa.decodeBE) + 1 := by
  rw [generationChunks_step hw h, List.map_cons, generatorCount]
  simp only [generatorHit, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Dsa.Generation
