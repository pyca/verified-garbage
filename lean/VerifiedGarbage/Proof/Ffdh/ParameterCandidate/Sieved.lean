module

public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream

/-! # The sieved candidate by its shape and its three tests

`sieved_eq`: once the tape holds the candidate's octets,
`Spec.Ffdh.sievedParameterCandidate` is its shape's checks, then
`sievedTests`: one witness of p, all of q's, then p's others, each test
ending the candidate unless it passed (`onPass`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

/-- After a test's result `res`: the candidate rejected unless it passed,
then `k` on the rest of the tape. -/
def onPass (res : Option (Bool × List Byte)) (k : List Byte → Option (Option Nat × List Byte)) :
    Option (Option Nat × List Byte) :=
  match res with
  | none => none
  | some (false, r) => some (none, r)
  | some (true, r) => k r

/-- The tests from the tape `r`: one witness of p, all of q's, then p's
others (`screenedChecks`). -/
def sievedTests (c : Nat) (r : List Byte) : Option (Option Nat × List Byte) :=
  onPass (checkWitnesses c 1 r) fun r =>
    onPass (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength ((c - 1) / 2))) r)
      fun r => (checkWitnesses c (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength c) - 1) r).map
        fun (pass, r) => (if pass then some c else none, r)

/-- The sieved candidate by its shape and its tests. -/
theorem sieved_eq {bits g : Nat} {r : List Byte} (h : (bits + 7) / 8 ≤ r.length) :
    Spec.Ffdh.sievedParameterCandidate bits g r =
      if !(Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) &&
          !Spec.RsaKeyGen.obviouslyComposite bits
            (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          !Spec.RsaKeyGen.obviouslyComposite bits
            ((Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2))
      then some (none, r.drop ((bits + 7) / 8))
      else sievedTests (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))))
        (r.drop ((bits + 7) / 8)) := by
  unfold Spec.Ffdh.sievedParameterCandidate
  rw [draw_of_le h]
  simp only [bind, Option.bind]
  generalize Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) = c
  generalize r.drop ((bits + 7) / 8) = t
  split
  · rfl
  · rename_i hcond
    have hc := Bool.not_eq_true _ ▸ hcond
    simp only [Bool.not_eq_false', Bool.and_eq_true] at hc
    rw [← screenedChecks_eq hc.1.1.1.2 hc.1.1.2]
    unfold screenedChecks sievedTests onPass
    rcases h1 : checkWitnesses c 1 t with _ | ⟨_ | _, t₁⟩
    · simp
    · simp
    rcases h2 : checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength ((c - 1) / 2))) t₁
      with _ | ⟨_ | _, t₂⟩
    · simp [h2]
    · simp [h2]
    rcases h3 : checkWitnesses c (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength c) - 1) t₂ with _ | ⟨_ | _, t₃⟩
    all_goals simp [h2, h3]

end VG.Proof.Ffdh.ParameterCandidate
