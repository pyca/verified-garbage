module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort

import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native controller's local transitions implement the complete search -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.Proof.Ffdh.Generation

def searchTail (p : SearchPublic) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  (Spec.Ffdh.parameterSearch p.c.bits p.c.gen remaining (p.c.rand.drop used)).consume used

theorem searchTail_zero (p : SearchPublic) (used : Nat) : searchTail p used 0 = .exhausted used := rfl

theorem searchTail_short {p : SearchPublic} {used remaining : Nat} (hr : 0 < remaining)
    (hc : searchCandidate p used = none) : searchTail p used remaining = shortResult p used remaining := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.parameterSearch, show Spec.Ffdh.parameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = none from hc]
    simp only [List.length_drop]
    by_cases hb : Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used <;>
      simp [hb, shortResult, Spec.Ffdh.ParameterSearchResult.consume]

theorem searchTail_accept {p : SearchPublic} {used remaining prime : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (some prime, rest)) :
    searchTail p used remaining = .accepted prime (used + (p.c.rand.length - used - rest.length)) := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.parameterSearch, show Spec.Ffdh.parameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = some (some prime, rest) from hc]
    simp only [Spec.Ffdh.ParameterSearchResult.consume, List.length_drop]

theorem searchTail_reject {p : SearchPublic} {used remaining : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (none, rest)) :
    searchTail p used remaining = searchTail p (used + (p.c.rand.length - used - rest.length))
      (remaining - 1) := by
  simpa only [searchTail, List.length_drop] using search_reject hr hc

end VG.Proof.Ffdh.X86_64.Generation
