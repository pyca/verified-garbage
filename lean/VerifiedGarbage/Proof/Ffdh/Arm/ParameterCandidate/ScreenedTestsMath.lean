module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Framework.Omega

/-! Public answers and entropy suffixes for early-p, full-q, remaining-p control flow. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Ffdh.ParameterCandidate

def continueWitnesses (answer : Option (Bool × List Byte)) (next : List Byte → Option (Bool × List Byte)) :
    Option (Bool × List Byte) := do
  let (pass, tail) ← answer
  if !pass then some (false, tail) else next tail

def screenedQTests (p : CandidateParams) (used : Nat) : Option (Bool × List Byte) :=
  continueWitnesses (witnessRemaining (candidatePhase p true) used 0)
    (checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits - 1))

def screenedTests (p : CandidateParams) (used : Nat) : Option (Bool × List Byte) :=
  continueWitnesses (witnessRemaining (limitedPhase p true) used 0) (fun tail =>
    continueWitnesses (checkWitnesses ((p.candidate - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) tail)
      (checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits - 1)))

theorem continueWitnesses_stop (answer : Option (Bool × List Byte)) (next : List Byte → Option (Bool × List Byte))
    (stop : witnessResultStatus answer ≠ 1) : continueWitnesses answer next = answer := by
  cases answer with
  | none => rfl
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    cases pass with
    | false => rfl
    | true => exact False.elim (stop rfl)

theorem continueWitnesses_go (answer : Option (Bool × List Byte)) (next : List Byte → Option (Bool × List Byte))
    {tail : List Byte} (go : witnessResultStatus answer = 1)
    (suffix : ∀ rest, answer = some (true, rest) → rest = tail) :
    continueWitnesses answer next = next tail := by
  cases answer with
  | none => change 0 = 1 at go; omega
  | some pair =>
    obtain ⟨pass, rest⟩ := pair
    cases pass with
    | false => change 2 = 1 at go; omega
    | true => rw [continueWitnesses, suffix rest rfl]; rfl

theorem screenedQTests_stop (p : CandidateParams) (used : Nat)
    (stop : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) ≠ 1) :
    screenedQTests p used = witnessRemaining (candidatePhase p true) used 0 :=
  continueWitnesses_stop _ _ stop

theorem screenedQTests_go (p : CandidateParams) (used next : Nat)
    (go : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) = 1)
    (suffix : ∀ pass rest, witnessRemaining (candidatePhase p true) used 0 = some (pass, rest) → rest = p.bytes.drop next) :
    screenedQTests p used = witnessRemaining (limitedPhase p false) next 0 :=
  continueWitnesses_go _ _ go (suffix true)

theorem screenedTests_stop (p : CandidateParams) (used : Nat)
    (stop : witnessResultStatus (witnessRemaining (limitedPhase p true) used 0) ≠ 1) :
    screenedTests p used = witnessRemaining (limitedPhase p true) used 0 :=
  continueWitnesses_stop _ _ stop

theorem screenedTests_go (p : CandidateParams) (used next : Nat)
    (go : witnessResultStatus (witnessRemaining (limitedPhase p true) used 0) = 1)
    (suffix : ∀ pass rest, witnessRemaining (limitedPhase p true) used 0 = some (pass, rest) → rest = p.bytes.drop next) :
    screenedTests p used = screenedQTests p next :=
  continueWitnesses_go _ _ go (suffix true)

end VG.Proof.Ffdh.Arm.ParameterCandidate
