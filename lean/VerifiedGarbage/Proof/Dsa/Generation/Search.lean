module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.List.Range

/-! # Equations for the finite parameter-generation controllers

These equations expose the reviewed specification's search order and tape
threading for native loops. A failed generator search restarts with the
next seed and the same original h tape, but the advanced witness tape.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

abbrev primeSearch (l n q : Nat) (seed : List Byte) (counter : Nat) (rand : Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.primeFromSeed.search l n q seed ((List.range (4 * l)).drop counter) rand

theorem primeSearch_start (l n q : Nat) (seed : List Byte) (rand : Spec.RsaKeyGen.Rand) :
    primeSearch l n q seed 0 rand = Spec.Dsa.primeFromSeed l n q seed rand := by
  simp only [primeSearch, List.drop_zero, Spec.Dsa.primeFromSeed]

theorem primeSearch_done {l n q counter : Nat} (seed : List Byte) (rand : Spec.RsaKeyGen.Rand)
    (hc : 4 * l ≤ counter) : primeSearch l n q seed counter rand = some (none, rand) := by
  rw [primeSearch, List.drop_eq_nil_of_le (by simpa using hc)]
  rfl

theorem primeSearch_step {l n q counter : Nat} (seed : List Byte) (rand : Spec.RsaKeyGen.Rand)
    (hc : counter < 4 * l) :
    primeSearch l n q seed counter rand =
      let p := Spec.Dsa.pCandidate l n q seed (1 + counter * ((l - 1) / n + 1))
      if p < 2 ^ (l - 1) then primeSearch l n q seed (counter + 1) rand
      else match Spec.Dsa.probablePrime p rand with
        | none => none
        | some (accepted, rest) =>
          if accepted then some (some p, rest) else primeSearch l n q seed (counter + 1) rest := by
  have he : (List.range (4 * l)).drop counter = counter :: (List.range (4 * l)).drop (counter + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hc)]
    simp
  simp only [primeSearch, he, Spec.Dsa.primeFromSeed.search]
  split
  · rfl
  · cases Spec.Dsa.probablePrime _ rand with
    | none => rfl
    | some pair => rcases pair with ⟨accepted, rest⟩; cases accepted <;> rfl

theorem generator_nil (p q : Nat) : Spec.Dsa.generator p q [] = none := rfl

theorem generator_cons (p q h : Nat) (hs : List Nat) :
    Spec.Dsa.generator p q (h :: hs) =
      if 1 < h ∧ h < p - 1 then
        let g := Spec.Dsa.powMod h ((p - 1) / q) p
        if 1 < g then some g else Spec.Dsa.generator p q hs
      else Spec.Dsa.generator p q hs := by
  simp only [Spec.Dsa.generator, List.filter_cons, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hh : 1 < h ∧ h < p - 1
  · simp only [hh, and_self, ite_true, List.map_cons, List.find?_cons]
    by_cases hg : 1 < Spec.Dsa.powMod h ((p - 1) / q) p <;> simp [hg]
  · simp only [hh, ite_false]

theorem parameterAttempt_nil (bits n : Nat) (hs : List Nat) (rand : Spec.RsaKeyGen.Rand) :
    Spec.Dsa.generateParameters.attempt bits hs n [] rand = none := rfl

/-- The h tape is an unchanged argument of every retry; only the witness
remainder returned by primality testing advances. -/
theorem parameterAttempt_step (bits n : Nat) (hs : List Nat) (seed : List Byte)
    (seeds : List (List Byte)) (rand : Spec.RsaKeyGen.Rand) (hlen : n ≤ 8 * seed.length) :
    Spec.Dsa.generateParameters.attempt bits hs n (seed :: seeds) rand =
      let q := Spec.Dsa.qCandidate n seed
      match Spec.Dsa.probablePrime q rand with
      | none => none
      | some (false, rest) => Spec.Dsa.generateParameters.attempt bits hs n seeds rest
      | some (true, rest) =>
        match Spec.Dsa.primeFromSeed bits n q seed rest with
        | none => none
        | some (none, rest') => Spec.Dsa.generateParameters.attempt bits hs n seeds rest'
        | some (some p, rest') =>
          match Spec.Dsa.generator p q hs with
          | none => Spec.Dsa.generateParameters.attempt bits hs n seeds rest'
          | some g =>
            if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩
            else Spec.Dsa.generateParameters.attempt bits hs n seeds rest' := by
  rw [Spec.Dsa.generateParameters.attempt]
  simp only [show ¬ 8 * seed.length < n by omega, ite_false]
  cases Spec.Dsa.probablePrime (Spec.Dsa.qCandidate n seed) rand with
  | none => rfl
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    cases accepted with
    | false => rfl
    | true =>
      simp only [bind, Option.bind, Bool.not_true, Bool.false_eq_true, ite_false]
      cases Spec.Dsa.primeFromSeed bits n (Spec.Dsa.qCandidate n seed) seed rest with
      | none => rfl
      | some pair =>
        rcases pair with ⟨p, rest'⟩
        cases p with
        | none => rfl
        | some p =>
          dsimp only
          cases Spec.Dsa.generator p (Spec.Dsa.qCandidate n seed) hs <;> rfl

end VG.Proof.Dsa.Generation
