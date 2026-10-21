module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! Each native transition preserves the shared complete-search result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Spec.Ffdh VG.Proof.Ffdh.SievedGeneration VG.Proof.Ffdh.ParameterCandidate

theorem SearchParams.tail_zero (p : SearchParams) (used : Nat) :
    p.tail used 0 = .exhausted used := rfl

theorem candidateUsed_bound (p : SearchParams) (used : Nat) :
    candidateUsed p used ≤ p.c.bytes.length - used := by
  unfold candidateUsed
  split <;> omega

theorem candidate_short (p : SearchParams) (used : Nat)
    (short : p.c.bytes.length - used < p.c.length) : candidateResult p used = none := by
  unfold candidateResult
  unfold Spec.Ffdh.sievedParameterCandidate
  have draw := draw_of_short (r := p.c.bytes.drop used) (len := p.c.length)
    (by simpa only [List.length_drop] using short)
  change VG.Spec.RsaKeyGen.draw ((p.c.bits + 7) / 8) (p.c.bytes.drop used) = none at draw
  rw [draw]
  rfl

theorem SearchParams.tail_short {p : SearchParams} {used remaining : Nat} (positive : 0 < remaining)
    (candidate : candidateResult p used = none) :
    p.tail used remaining = if Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.bytes.length - used
      then .exhausted used else .entropy remaining (parameterRequest p.c.bits (p.c.bytes.length - used)) used := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop]
    split <;> rfl

theorem SearchParams.tail_accept {p : SearchParams} {used remaining prime : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (some prime, rest)) :
    p.tail used remaining = .accepted prime (used + candidateUsed p used) := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop, ParameterSearchResult.consume, candidateUsed, candidateResult, candidate]

theorem SearchParams.tail_reject {p : SearchParams} {used remaining : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (none, rest)) :
    p.tail used remaining = p.tail (used + candidateUsed p used) (remaining - 1) := by
  have step := search_reject positive candidate
  simpa only [SearchParams.tail, candidateUsed, candidate, List.length_drop] using step

end VG.Proof.Ffdh.Arm.ParameterSearch
