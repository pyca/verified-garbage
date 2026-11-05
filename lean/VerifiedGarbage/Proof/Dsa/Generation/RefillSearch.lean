module

public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent facts about the spec, for every target's proof of the search

/-! # The refillable-tape parameter search, one seed at a time

`Spec.Dsa.parameterSearch` over a tape `R`, after `c` octets consumed by
rejected seeds: the native controller's invariant is that the whole search's
result is the search from `R.drop c`, with those `c` octets consumed before
it. Each lemma here is one way a step of the controller ends: no seeds left,
a tape too short for the next seed, or the seed's attempt (`refillAttempt`,
`RefillSeed.lean`) running out, rejecting the seed or accepting
parameters. -/

@[expose] public section

namespace VG.Proof.Dsa.Generation

open VG Spec.Dsa

theorem refillAttempt_suffix {pLen qLen : Nat} {seed rest r : List Byte} {x : Option Params}
    (h : refillAttempt pLen qLen seed rest = some (x, r)) : r <:+ rest := by
  unfold refillAttempt at h
  dsimp only at h
  rcases hq : probablePrime (qCandidate (8 * qLen) seed) rest with _ | ⟨_ | _, r₁⟩ <;> rw [hq] at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact probablePrime_suffix hq
  · have h₁ := probablePrime_suffix hq
    dsimp only at h
    rcases hp : primeFromSeed (8 * pLen) (8 * qLen) (qCandidate (8 * qLen) seed) seed r₁ with
      _ | ⟨_ | p, r₂⟩ <;> rw [hp] at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact (primeSearch_suffix seed _ r₁ hp).trans h₁
    · have h₂ := (primeSearch_suffix seed _ r₁ hp).trans h₁
      dsimp only at h
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h; exact (List.drop_suffix _ _).trans h₂
        · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact (List.drop_suffix _ _).trans h₂

theorem consume_consume (r : ParameterSearchResult) (a b : Nat) :
    (r.consume b []).consume a [] = r.consume (a + b) [] := by
  simp only [Spec.Entropy.Result.consume, Nat.add_assoc, List.nil_append]

/-- How a search ends with a tape too short for its next seed, `available`
octets left after `c` consumed, and `k` seeds it may still reject. -/
def ranOutResult (pLen k available c : Nat) : ParameterSearchResult :=
  if parameterEntropy pLen ≤ available then ⟨.exhausted, c, []⟩
  else ⟨.entropy k (parameterRequest pLen available), c, []⟩

theorem search_zero (pLen : Nat) (R : List Byte) (c : Nat) :
    (parameterSearch pLen 0 R).consume c [] = ⟨.exhausted, c, []⟩ := by
  simp [parameterSearch, Spec.Entropy.Result.consume]

theorem search_none {pLen k c : Nat} {R : List Byte}
    (h : seedCandidate pLen (generationQLen pLen) (R.drop c) = none) :
    (parameterSearch pLen (k + 1) (R.drop c)).consume c [] = ranOutResult pLen (k + 1) (R.length - c) c := by
  simp only [parameterSearch, h, ranOutResult, List.length_drop]
  split <;> simp [Spec.Entropy.Result.consume]

theorem search_short {pLen k c : Nat} {R : List Byte} (hc : R.length - c < generationQLen pLen) :
    (parameterSearch pLen (k + 1) (R.drop c)).consume c [] = ranOutResult pLen (k + 1) (R.length - c) c :=
  search_none (by rw [seedCandidate]; simp only [List.length_drop, hc, ↓reduceIte])

theorem seedCandidate_drop {pLen c : Nat} (hw : 0 < pLen) {R : List Byte}
    (hc : c + generationQLen pLen ≤ R.length) :
    seedCandidate pLen (generationQLen pLen) (R.drop c) =
      refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
        (R.drop (c + generationQLen pLen)) := by
  rw [seedCandidate_eq hw]
  simp only [List.length_drop, show ¬R.length - c < generationQLen pLen by omega, ↓reduceIte, List.drop_drop]

theorem search_attemptNone {pLen k c : Nat} (hw : 0 < pLen) {R : List Byte}
    (hc : c + generationQLen pLen ≤ R.length)
    (h : refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
      (R.drop (c + generationQLen pLen)) = none) :
    (parameterSearch pLen (k + 1) (R.drop c)).consume c [] = ranOutResult pLen (k + 1) (R.length - c) c :=
  search_none (by rw [seedCandidate_drop hw hc, h])

theorem attempt_used {pLen c u : Nat} {R : List Byte} {x : Option Params}
    (hc : c + generationQLen pLen ≤ R.length) (hu : u ≤ R.length)
    (h : refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
      (R.drop (c + generationQLen pLen)) = some (x, R.drop u)) :
    c + generationQLen pLen ≤ u := by
  have hs := (refillAttempt_suffix h).length_le
  simp only [List.length_drop] at hs
  omega

theorem search_rejected {pLen k c u : Nat} (hw : 0 < pLen) {R : List Byte}
    (hc : c + generationQLen pLen ≤ R.length) (hu : u ≤ R.length)
    (h : refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
      (R.drop (c + generationQLen pLen)) = some (none, R.drop u)) :
    (parameterSearch pLen (k + 1) (R.drop c)).consume c [] = (parameterSearch pLen k (R.drop u)).consume u [] := by
  have hcu := attempt_used hc hu h
  rw [parameterSearch, seedCandidate_drop hw hc, h]
  dsimp only
  rw [consume_consume]
  simp only [List.length_drop]
  congr 1
  omega

theorem search_accepted {pLen k c u : Nat} (hw : 0 < pLen) {R : List Byte} {a : Params}
    (hc : c + generationQLen pLen ≤ R.length) (hu : u ≤ R.length)
    (h : refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
      (R.drop (c + generationQLen pLen)) = some (some a, R.drop u)) :
    (parameterSearch pLen (k + 1) (R.drop c)).consume c [] = ⟨.accepted a, u, []⟩ := by
  have hcu := attempt_used hc hu h
  rw [parameterSearch, seedCandidate_drop hw hc, h]
  simp only [List.length_drop, Spec.Entropy.Result.consume, List.append_nil, Spec.Entropy.Result.mk.injEq,
    true_and, and_true]
  omega

end VG.Proof.Dsa.Generation
