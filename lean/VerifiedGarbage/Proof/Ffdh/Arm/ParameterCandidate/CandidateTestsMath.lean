module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Framework.Omega

/-! The candidate controller runs q first and consumes p witnesses only after q passes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Ffdh.ParameterCandidate

def candidateTests (p : CandidateParams) (used : Nat) : Option (Bool × List Byte) := do
  let (pass, tail) ← witnessRemaining (candidatePhase p true) used 0
  if pass then checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits) tail else some (false, tail)

theorem candidateTests_stop (p : CandidateParams) (used : Nat)
    (stop : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) ≠ 1) :
    candidateTests p used = witnessRemaining (candidatePhase p true) used 0 := by
  unfold candidateTests
  cases answer : witnessRemaining (candidatePhase p true) used 0 with
  | none => rfl
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    cases pass with
    | false => rfl
    | true => exact False.elim (stop (by rw [answer]; rfl))

theorem candidateTests_go (p : CandidateParams) (used next : Nat)
    (go : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) = 1)
    (suffix : ∀ pass rest, witnessRemaining (candidatePhase p true) used 0 = some (pass, rest) → rest = p.bytes.drop next) :
    candidateTests p used = witnessRemaining (candidatePhase p false) next 0 := by
  unfold candidateTests
  cases answer : witnessRemaining (candidatePhase p true) used 0 with
  | none => rw [answer] at go; change 0 = 1 at go; omega
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    cases pass with
    | false => rw [answer] at go; change 2 = 1 at go; omega
    | true =>
      rw [suffix true tail answer]
      rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
