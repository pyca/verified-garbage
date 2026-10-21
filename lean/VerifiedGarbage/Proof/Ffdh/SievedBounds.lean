module

public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
import VerifiedGarbage.Proof.Ffdh.SievedTape
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Omega

/-! The RSA-sieved search preserves existing entropy, attempt and refill bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.SievedGeneration
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.Generation

theorem search_used_le (bits generator : Nat) : ∀ remaining r,
    (sievedParameterSearch bits generator remaining r).used ≤ r.length := by
  intro remaining
  induction remaining with
  | zero => intro r; exact Nat.zero_le _
  | succ remaining ih =>
    intro r
    rw [sievedParameterSearch]
    cases he : sievedParameterCandidate bits generator r with
    | none => dsimp only; split <;> exact Nat.zero_le _
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none =>
        rw [consume_used]
        obtain ⟨used, hu, hr⟩ := candidate_suffix he
        have hi := ih rest
        rw [hr, List.length_drop] at hi
        simp only [hr, List.length_drop]
        omega_using [hu, hi]
      | some p => exact Nat.sub_le _ _

theorem search_remaining_le (bits generator : Nat) : ∀ remaining r,
    (sievedParameterSearch bits generator remaining r).remaining ≤ remaining := by
  intro remaining
  induction remaining with
  | zero => intro r; exact Nat.zero_le _
  | succ remaining ih =>
    intro r
    rw [sievedParameterSearch]
    cases he : sievedParameterCandidate bits generator r with
    | none => dsimp only; split <;> simp only [ParameterSearchResult.remaining] <;> omega
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none => rw [consume_remaining]; exact Nat.le_trans (ih rest) (Nat.le_succ _)
      | some p => exact Nat.zero_le _

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
