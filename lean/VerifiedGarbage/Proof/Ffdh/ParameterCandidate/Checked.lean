module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream

/-!
# An FFDH parameter candidate: its tests

`testsSpec`: the tests of q and then p, once the shape passed;
`checked_eq`: `checkedCandidate` by its shape and its tests.
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

/-- The tests of `q` and then `p`, from the tape `r`. -/
def testsSpec (c : Nat) (r : List Byte) : Option (Option Nat × List Byte) := do
  let (qpass, r) ← checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength ((c - 1) / 2))) r
  if !qpass then return (none, r)
  let (ppass, r) ← checkWitnesses c (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength c)) r
  return (if ppass then some c else none, r)

theorem checked_eq {bits g : Nat} {r : List Byte} (h : (bits + 7) / 8 ≤ r.length) :
    checkedCandidate bits g r =
      if !(Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2))
      then some (none, r.drop ((bits + 7) / 8))
      else testsSpec (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))))
        (r.drop ((bits + 7) / 8)) := by
  simp only [checkedCandidate, draw_of_le h, bind, Option.bind]
  rfl

end VG.Proof.Ffdh.ParameterCandidate
