module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Generation.Search

/-! # One seed result, retaining the witness suffix for the outer retry -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

def generatorResult (p q : Nat) (hs : List Nat) (rand : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.generator p q hs with
  | none => some (none, rand)
  | some g => if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some (some ⟨p, q, g⟩, rand) else some (none, rand)

def primeResult (l n q : Nat) (seed : List Byte) (hs : List Nat) (rand : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.primeFromSeed l n q seed rand with
  | none => none
  | some (none, rest) => some (none, rest)
  | some (some p, rest) => generatorResult p q hs rest

def seedResult (l n : Nat) (seed : List Byte) (hs : List Nat) (rand : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  let q := Spec.Dsa.qCandidate n seed
  match Spec.Dsa.probablePrime q rand with
  | none => none
  | some (false, rest) => some (none, rest)
  | some (true, rest) => primeResult l n q seed hs rest

theorem parameterAttempt_seedResult (l n : Nat) (hs : List Nat) (seed : List Byte)
    (seeds : List (List Byte)) (rand : List Byte) (hlen : n ≤ 8 * seed.length) :
    Spec.Dsa.generateParameters.attempt l hs n (seed :: seeds) rand =
      match seedResult l n seed hs rand with
      | none => none
      | some (none, rest) => Spec.Dsa.generateParameters.attempt l hs n seeds rest
      | some (some params, _) => some params := by
  rw [parameterAttempt_step l n hs seed seeds rand hlen]
  unfold seedResult
  dsimp only
  cases hq : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate n seed) rand with
  | none => rfl
  | some result =>
    rcases result with ⟨accepted, rest⟩
    cases accepted with
    | false => rfl
    | true =>
      dsimp only
      unfold primeResult
      cases hp : Spec.Dsa.primeFromSeed l n (Spec.Dsa.qCandidate n seed) seed rest with
      | none => rfl
      | some result =>
        rcases result with ⟨p, rest'⟩
        cases p with
        | none => rfl
        | some p =>
          dsimp only
          unfold generatorResult
          cases hg : Spec.Dsa.generator p (Spec.Dsa.qCandidate n seed) hs with
          | none => rfl
          | some g => dsimp only; split <;> rfl

end VG.Proof.Dsa.Generation
