module

public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Ffdh.SievedTape
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream

/-! # The sieved parameter search from an offset into the tape

`ptail` is the search from octet `used` of the tape with `n` attempts left,
counting the octets consumed from the tape's start, as the controller's loop
tracks it; each of its cases after a candidate (`ptail_short`,
`ptail_accept`, `ptail_reject`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand)

/-- The search from octet `used` of `rand`, with `n` attempts left. -/
def ptail (bits gen : Nat) (rand : Rand) (used n : Nat) : ParameterSearchResult :=
  (sievedParameterSearch bits gen n (rand.drop used)).consume used

/-- The candidate at octet `used`. -/
abbrev candAt (bits gen : Nat) (rand : Rand) (used : Nat) : Option (Option Nat × Rand) :=
  sievedParameterCandidate bits gen (rand.drop used)

/-- The octets the candidate at `used` consumes: none on a shortage. -/
def candUsed (bits gen : Nat) (rand : Rand) (used : Nat) : Nat :=
  match candAt bits gen rand used with
  | some (_, rest) => (rand.length - used) - rest.length
  | none => 0

theorem ptail_zero (bits gen : Nat) (rand : Rand) (used : Nat) : ptail bits gen rand used 0 = .exhausted used := by
  simp only [ptail, sievedParameterSearch, ParameterSearchResult.consume, Nat.add_zero]

theorem candUsed_le (bits gen : Nat) (rand : Rand) (used : Nat) : candUsed bits gen rand used ≤ rand.length - used := by
  unfold candUsed
  split <;> omega

theorem cand_short {bits gen : Nat} {rand : Rand} {used : Nat} (h : rand.length - used < (bits + 7) / 8) :
    candAt bits gen rand used = none := by
  unfold candAt sievedParameterCandidate
  rw [ParameterCandidate.draw_of_short (by rw [List.length_drop]; exact h)]
  rfl

theorem ptail_short {bits gen : Nat} {rand : Rand} {used n : Nat} (hn : n ≠ 0) (h : candAt bits gen rand used = none) :
    ptail bits gen rand used n = if parameterEntropy bits ≤ rand.length - used then .exhausted used
      else .entropy n (parameterRequest bits (rand.length - used)) used := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold ptail
  rw [sievedParameterSearch, show sievedParameterCandidate bits gen (rand.drop used) = none from h]
  simp only [List.length_drop]
  split <;> simp only [ParameterSearchResult.consume, Nat.add_zero]

theorem ptail_accept {bits gen : Nat} {rand : Rand} {used n p : Nat} {rest : Rand} (hn : n ≠ 0)
    (h : candAt bits gen rand used = some (some p, rest)) :
    ptail bits gen rand used n = .accepted p (used + candUsed bits gen rand used) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold ptail candUsed
  rw [sievedParameterSearch, show sievedParameterCandidate bits gen (rand.drop used) = some (some p, rest) from h]
  simp only [List.length_drop, ParameterSearchResult.consume, h]

theorem ptail_reject {bits gen : Nat} {rand : Rand} {used n : Nat} {rest : Rand} (hn : n ≠ 0)
    (h : candAt bits gen rand used = some (none, rest)) :
    ptail bits gen rand used n = ptail bits gen rand (used + candUsed bits gen rand used) (n - 1) := by
  have step := SievedGeneration.search_reject (by omega : 0 < n) h
  simpa only [ptail, candUsed, h, List.length_drop] using step

end VG.Proof.Ffdh.X86.PSearch
