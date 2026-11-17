module

public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream

/-! ### `Ffdh.GenerationTape`, which only this module used -/

section

/-! # A witness batch consumes a prefix of the tape, including every rejected witness -/

@[expose] public section

namespace VG.Proof.Ffdh.Generation

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.ParameterCandidate

theorem checkWitnesses_suffix {w : Nat} (hn : 0 < witnessOctets w) :
    ∀ n r pass rest, checkWitnesses w n r = some (pass, rest) →
      ∃ used ≤ r.length, rest = r.drop used := by
  intro n
  induction n with
  | zero =>
    intro r pass rest he
    simp only [checkWitnesses, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨0, Nat.zero_le _, by simpa only [List.drop_zero] using he.2.symm⟩
  | succ n ih =>
    intro r pass rest he
    simp only [checkWitnesses, bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨a, r'⟩, ha, he⟩ := he
    obtain ⟨used, _, hu, hr⟩ := drawWitness_suffix hn r a r' ha
    dsimp only at he
    split at he
    · obtain ⟨more, hm, ht⟩ := ih _ _ _ he
      refine ⟨used + more, ?_, ?_⟩
      · rw [hr, List.length_drop] at hm
        omega_using [hm, hu]
      · rw [ht, hr, List.drop_drop]
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨used, hu, he.2.symm.trans hr⟩

end VG.Proof.Ffdh.Generation

end

end

/-! ### `Ffdh.GenerationBounds`, which this module and modules that import it used -/

section

/-! # Native generation control: byte accounting and bounded persistent state -/

@[expose] public section

namespace VG.Proof.Ffdh.Generation

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem consume_assoc (result : ParameterSearchResult) (a b : Nat) :
    (result.consume b).consume a = result.consume (a + b) := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.add_assoc]

theorem consume_zero (result : ParameterSearchResult) : result.consume 0 = result := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.zero_add]

end VG.Proof.Ffdh.Generation

end

end

/-! ### `Ffdh.SievedTape`, which this module and modules that import it used -/

section

/-! The RSA-sieved candidate and each witness batch consume only a bounded entropy prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.SievedGeneration
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.ParameterCandidate

private theorem suffix_trans {r middle rest : Rand}
    (first : ∃ used ≤ r.length, middle = r.drop used)
    (second : ∃ used ≤ middle.length, rest = middle.drop used) :
    ∃ used ≤ r.length, rest = r.drop used := by
  obtain ⟨a, boundA, mid⟩ := first
  obtain ⟨b, boundB, last⟩ := second
  refine ⟨a + b, ?_, ?_⟩
  · rw [mid, List.length_drop] at boundB
    omega_using [boundA, boundB]
  · rw [last, mid, List.drop_drop]

private theorem width_pos {w : Nat} (shape : primeShape w = true) : 0 < witnessOctets w := by
  have large : 2 < w := by
    simp only [primeShape, Bool.and_eq_true, decide_eq_true_eq] at shape
    exact shape.1.1
  have nonzero : w - 1 ≠ 0 := by omega_using [large]
  simp only [witnessOctets, bitLength, nonzero, ite_false]
  omega_using []

private theorem checks_suffix {p q : Nat} {r rest : Rand} {pass : Bool}
    (shapeP : primeShape p = true) (shapeQ : primeShape q = true)
    (run : screenedParameterWitnesses p q r = some (pass, rest)) :
    ∃ used ≤ r.length, rest = r.drop used := by
  rw [← screenedChecks_eq shapeP shapeQ] at run
  unfold screenedChecks at run
  simp only [bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨first, afterP⟩, firstRun, run⟩ := run
  have prefixP := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeP) _ _ _ _ firstRun
  dsimp only at run
  split at run
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
    exact run.2 ▸ prefixP
  · simp only [Option.bind_eq_some_iff] at run
    obtain ⟨⟨qpass, afterQ⟩, qRun, run⟩ := run
    have prefixQ := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeQ) _ _ _ _ qRun
    dsimp only at run
    split at run
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact run.2 ▸ suffix_trans prefixP prefixQ
    · have prefixRest := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeP) _ _ _ _ run
      exact suffix_trans prefixP (suffix_trans prefixQ prefixRest)

theorem candidate_suffix {bits generator : Nat} {r rest : Rand} {p : Option Nat}
    (run : sievedParameterCandidate bits generator r = some (p, rest)) :
    ∃ used ≤ r.length, rest = r.drop used := by
  unfold sievedParameterCandidate at run
  by_cases enough : (bits + 7) / 8 ≤ r.length
  · rw [draw_of_le enough] at run
    simp only [bind, Option.bind_some] at run
    split at run
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact ⟨(bits + 7) / 8, enough, run.2.symm⟩
    · rename_i valid
      have shapes := Bool.eq_false_iff.mpr valid
      simp only [Bool.not_eq_false', Bool.and_eq_true] at shapes
      simp only [Option.bind_eq_some_iff] at run
      obtain ⟨⟨pass, tail⟩, witnesses, run⟩ := run
      have after := checks_suffix shapes.1.1.1.2 shapes.1.1.2 witnesses
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact run.2 ▸ suffix_trans ⟨(bits + 7) / 8, enough, rfl⟩ after
  · rw [draw_of_short (by omega_using [enough] : r.length < (bits + 7) / 8)] at run
    cases run

end VG.Proof.Ffdh.SievedGeneration

end

end

/-! The RSA-sieved search preserves existing entropy, attempt and refill bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.SievedGeneration
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.Generation

/-- Asking for more entropy, the search had fewer octets left than its budget. -/
theorem search_available_lt (bits generator : Nat) : ∀ remaining r k a u,
    sievedParameterSearch bits generator remaining r = .entropy k a u → a < parameterEntropy bits := by
  intro remaining
  induction remaining with
  | zero => intro r k a u h; cases h
  | succ remaining ih =>
    intro r k a u h
    rw [sievedParameterSearch] at h
    cases he : sievedParameterCandidate bits generator r with
    | none =>
      rw [he] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hlt
        cases h
        omega_using [hlt]
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      rw [he] at h
      cases value with
      | none =>
        dsimp only at h
        cases hs : sievedParameterSearch bits generator remaining rest with
        | entropy k' a' u' =>
          rw [hs] at h
          simp only [ParameterSearchResult.consume, ParameterSearchResult.entropy.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact ih rest _ _ _ hs
        | accepted => rw [hs] at h; cases h
        | exhausted => rw [hs] at h; cases h
      | some p => cases h

/-- The code's request after any search is one the contract allows. -/
theorem search_requests (bits generator remaining : Nat) (r : Rand) :
    (sievedParameterSearch bits generator remaining r).Requests (parameterEntropy bits)
      (Proof.Ffdh.requested bits (sievedParameterSearch bits generator remaining r)) :=
  Proof.Ffdh.requested_requests fun k a u h => by
    have hlt := search_available_lt bits generator remaining r k a u h
    exact Entropy.request_valid (by unfold parameterEntropy at hlt; omega_using [hlt]) hlt

theorem candidate_rest {bits generator : Nat} {rand rest : Rand} {value : Option Nat}
    (h : sievedParameterCandidate bits generator rand = some (value, rest)) :
    rest = rand.drop (rand.length - rest.length) := by
  obtain ⟨used, hu, hr⟩ := candidate_suffix h
  have hl : rand.length - rest.length = used := by
    rw [hr, List.length_drop]
    omega_using [hu]
  rw [hl]
  exact hr

theorem search_reject {bits generator remaining used : Nat} {rand rest : Rand}
    (hr : 0 < remaining)
    (hc : sievedParameterCandidate bits generator (rand.drop used) = some (none, rest)) :
    (sievedParameterSearch bits generator remaining (rand.drop used)).consume used =
      (sievedParameterSearch bits generator (remaining - 1)
        (rand.drop (used + ((rand.drop used).length - rest.length)))).consume
        (used + ((rand.drop used).length - rest.length)) := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    rw [sievedParameterSearch, hc, consume_assoc, Nat.add_sub_cancel]
    have he : rest = rand.drop (used + ((rand.drop used).length - rest.length)) :=
      (candidate_rest hc).trans List.drop_drop
    exact congrArg (fun r => (sievedParameterSearch bits generator n r).consume
      (used + ((rand.drop used).length - rest.length))) he

end VG.Proof.Ffdh.SievedGeneration
