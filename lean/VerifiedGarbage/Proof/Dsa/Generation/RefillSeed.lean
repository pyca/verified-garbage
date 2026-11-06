module

public import VerifiedGarbage.Spec.Dsa.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Framework.Omega

/-! # One seed of the refillable-tape parameter search, as native code runs it

`Spec.Dsa.seedCandidate` draws the generator's `h` candidates from the tape
after the seed's witnesses. Native code runs the list generator search
`Spec.Dsa.generator` over a window of the tape: its first
`generatorAttempts` candidates' octets, or fewer if the tape is shorter
(`generatorSearch_window`). `refillAttempt` is the seed's result in those
terms: the witness tape's rest after `p`'s tests, the generator over the
window, and the candidates it read (`generatorCount`); a window cut short by
the tape's end, without a generator, ran out of entropy. -/

@[expose] public section

namespace VG.Proof.Dsa.Generation

open VG

/-- The `h` candidates of the window at `rest`: its first `fuel` whole
candidates of `pLen` octets. -/
def windowCandidates (pLen fuel : Nat) (rest : List Byte) : List Nat :=
  (Spec.Dsa.generationChunks pLen (rest.take (fuel * pLen))).map Spec.Dsa.decodeBE

theorem generatorHit_iff (p q h : Nat) :
    generatorHit p q h = true ↔ (1 < h ∧ h < p - 1) ∧ 1 < Spec.Dsa.powMod h ((p - 1) / q) p := by
  simp [generatorHit]

theorem generator_cons' (p q h : Nat) (hs : List Nat) :
    Spec.Dsa.generator p q (h :: hs) =
      if generatorHit p q h then some (Spec.Dsa.powMod h ((p - 1) / q) p) else Spec.Dsa.generator p q hs := by
  rw [generator_cons]
  by_cases hh : 1 < h ∧ h < p - 1
  · by_cases hg : 1 < Spec.Dsa.powMod h ((p - 1) / q) p
    · simp [hh, hg, generatorHit]
    · have : generatorHit p q h = false := by simp [generatorHit, hg]
      simp [hh, hg, this]
  · have : generatorHit p q h = false := by
      cases e : generatorHit p q h
      · rfl
      · exact absurd ((generatorHit_iff _ _ _).mp e).1 hh
    simp [hh, this]

theorem generatorSearch_succ {p q pLen fuel : Nat} {rest : List Byte} (hr : pLen ≤ rest.length) :
    Spec.Dsa.generatorSearch p q pLen (fuel + 1) rest =
      if generatorHit p q (Spec.Dsa.decodeBE (rest.take pLen)) then
        some (some (Spec.Dsa.powMod (Spec.Dsa.decodeBE (rest.take pLen)) ((p - 1) / q) p), rest.drop pLen)
      else Spec.Dsa.generatorSearch p q pLen fuel (rest.drop pLen) := by
  rw [Spec.Dsa.generatorSearch]
  simp only [show ¬rest.length < pLen by omega, ↓reduceIte]
  by_cases hh : (1 < Spec.Dsa.decodeBE (rest.take pLen) && Spec.Dsa.decodeBE (rest.take pLen) < p - 1) = true
  · by_cases hg : 1 < Spec.Dsa.powMod (Spec.Dsa.decodeBE (rest.take pLen)) ((p - 1) / q) p
    · have : generatorHit p q (Spec.Dsa.decodeBE (rest.take pLen)) = true := by
        simp only [generatorHit, hh, Bool.true_and, decide_eq_true_eq]; exact hg
      simp only [hh, hg, this, ite_true]
    · have : generatorHit p q (Spec.Dsa.decodeBE (rest.take pLen)) = false := by
        simp only [generatorHit, hh, Bool.true_and, decide_eq_false_iff_not]; exact hg
      simp only [hh, hg, this, ite_true, ite_false, Bool.false_eq_true]
  · have : generatorHit p q (Spec.Dsa.decodeBE (rest.take pLen)) = false := by
      simp only [generatorHit, Bool.and_eq_false_iff]; left; exact Bool.and_eq_false_iff.mp (Bool.eq_false_iff.mpr hh)
    simp only [hh, this, ite_false, Bool.false_eq_true]

/-- The spec's generator search over the tape, as `generator` over its
window: the generator and the candidates it read, or, without one, all
`fuel` candidates if the tape held them and an exhausted tape otherwise. -/
theorem generatorSearch_window {pLen : Nat} (hw : 0 < pLen) (p q : Nat) :
    ∀ (fuel : Nat) (rest : List Byte),
      Spec.Dsa.generatorSearch p q pLen fuel rest =
        match Spec.Dsa.generator p q (windowCandidates pLen fuel rest) with
        | some g => some (some g, rest.drop (pLen * generatorCount p q (windowCandidates pLen fuel rest)))
        | none => if fuel * pLen ≤ rest.length then some (none, rest.drop (fuel * pLen)) else none
  | 0, rest => by
    simp [Spec.Dsa.generatorSearch, windowCandidates, Spec.Dsa.generationChunks, generator_nil]
  | fuel + 1, rest => by
    by_cases hr : rest.length < pLen
    · have hc : windowCandidates pLen (fuel + 1) rest = [] := by
        rw [windowCandidates, generationChunks_done (by simp only [List.length_take]; omega), List.map_nil]
      rw [hc, generator_nil, Spec.Dsa.generatorSearch]
      simp only [hr, ↓reduceIte, show ¬(fuel + 1) * pLen ≤ rest.length by rw [Nat.succ_mul]; omega]
    · have hlen : pLen ≤ (rest.take ((fuel + 1) * pLen)).length := by
        simp only [List.length_take]; rw [Nat.succ_mul]; omega
      have hc : windowCandidates pLen (fuel + 1) rest =
          Spec.Dsa.decodeBE (rest.take pLen) :: windowCandidates pLen fuel (rest.drop pLen) := by
        rw [windowCandidates, generationChunks_step hw hlen, List.map_cons, windowCandidates,
          List.take_take, Nat.min_eq_left (by rw [Nat.succ_mul]; omega), List.drop_take,
          show (fuel + 1) * pLen - pLen = fuel * pLen by rw [Nat.succ_mul]; omega]
      rw [generatorSearch_succ (by omega), hc, generator_cons']
      by_cases hit : generatorHit p q (Spec.Dsa.decodeBE (rest.take pLen)) = true
      · simp only [hit, ite_true, generatorCount, Nat.mul_one]
      · simp only [hit, ite_false, Bool.false_eq_true, generatorCount]
        rw [generatorSearch_window hw p q fuel (rest.drop pLen)]
        cases Spec.Dsa.generator p q (windowCandidates pLen fuel (rest.drop pLen)) with
        | some g =>
          simp only [List.drop_drop, Nat.mul_succ]
          congr 3; omega
        | none =>
          simp only [List.length_drop, List.drop_drop]
          by_cases hf : fuel * pLen ≤ rest.length - pLen
          · simp only [hf, ↓reduceIte, show (fuel + 1) * pLen ≤ rest.length by rw [Nat.succ_mul]; omega]
            congr 3; rw [Nat.succ_mul]; omega
          · simp only [hf, ↓reduceIte, show ¬(fuel + 1) * pLen ≤ rest.length by rw [Nat.succ_mul]; omega]

/-- One seed after its own octets, with `rest` the tape after them: `q`'s
test, the `p` search and, over the window after `p`'s witnesses, the
generator and the parameters' validation. -/
def refillAttempt (pLen qLen : Nat) (seed rest : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  let q := Spec.Dsa.qCandidate (8 * qLen) seed
  match Spec.Dsa.probablePrime q rest with
  | none => none
  | some (false, r) => some (none, r)
  | some (true, r) =>
    match Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) q seed r with
    | none => none
    | some (none, r') => some (none, r')
    | some (some p, r') =>
      let hs := windowCandidates pLen Spec.Dsa.generatorAttempts r'
      match Spec.Dsa.generator p q hs with
      | none =>
        if Spec.Dsa.generatorAttempts * pLen ≤ r'.length then
          some (none, r'.drop (Spec.Dsa.generatorAttempts * pLen))
        else none
      | some g =>
        some (if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none,
          r'.drop (pLen * generatorCount p q hs))

theorem seedCandidate_eq {pLen : Nat} (hw : 0 < pLen) (qLen : Nat) (rand : List Byte) :
    Spec.Dsa.seedCandidate pLen qLen rand =
      if rand.length < qLen then none else refillAttempt pLen qLen (rand.take qLen) (rand.drop qLen) := by
  by_cases hr : rand.length < qLen
  · simp [Spec.Dsa.seedCandidate, hr]
  · simp only [Spec.Dsa.seedCandidate, refillAttempt, hr, ↓reduceIte]
    cases hq : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) (rand.take qLen)) (rand.drop qLen) with
    | none => rfl
    | some pair =>
      rcases pair with ⟨accepted, r⟩
      cases accepted
      · rfl
      · cases hp : Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) (Spec.Dsa.qCandidate (8 * qLen) (rand.take qLen))
            (rand.take qLen) r with
        | none => simp [hp]
        | some pair' =>
          rcases pair' with ⟨p, r'⟩
          cases p with
          | none => simp [hp]
          | some p =>
            simp only [hp, Option.bind_eq_bind, Option.bind_some, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, generatorSearch_window hw]
            cases Spec.Dsa.generator p _ (windowCandidates pLen Spec.Dsa.generatorAttempts r') with
            | some g => rfl
            | none => by_cases hl : Spec.Dsa.generatorAttempts * pLen ≤ r'.length <;> simp [hl]

end VG.Proof.Dsa.Generation
