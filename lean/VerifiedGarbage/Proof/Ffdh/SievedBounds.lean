module

public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Ffdh.SievedTape
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Omega

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
        omega
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
    exact Entropy.request_valid (by unfold parameterEntropy at hlt; omega) hlt

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
