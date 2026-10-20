module
public import VerifiedGarbage.Spec.Ffdh.Generation

import VerifiedGarbage.Proof.Ffdh.GenerationTape
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native generation control: byte accounting and bounded persistent state -/

@[expose] public section

namespace VG.Proof.Ffdh.Generation

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem consume_used (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).used = n + result.used := by
  cases result <;> rfl

theorem consume_remaining (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).remaining = result.remaining := by
  cases result <;> rfl

theorem consume_requested (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).requested = result.requested := by
  cases result <;> rfl

theorem consume_assoc (result : ParameterSearchResult) (a b : Nat) :
    (result.consume b).consume a = result.consume (a + b) := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.add_assoc]

theorem consume_status (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).status = result.status := by
  cases result <;> rfl

theorem consume_zero (result : ParameterSearchResult) : result.consume 0 = result := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.zero_add]

theorem search_used_le (bits generator : Nat) : ∀ remaining r,
    (parameterSearch bits generator remaining r).used ≤ r.length := by
  intro remaining
  induction remaining with
  | zero => intro r; exact Nat.zero_le _
  | succ remaining ih =>
    intro r
    rw [parameterSearch]
    cases he : parameterCandidate bits generator r with
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
    (parameterSearch bits generator remaining r).remaining ≤ remaining := by
  intro remaining
  induction remaining with
  | zero => intro r; exact Nat.zero_le _
  | succ remaining ih =>
    intro r
    rw [parameterSearch]
    cases he : parameterCandidate bits generator r with
    | none => dsimp only; split <;> simp only [ParameterSearchResult.remaining] <;> omega
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none => rw [consume_remaining]; exact Nat.le_trans (ih rest) (Nat.le_succ _)
      | some p => exact Nat.zero_le _

theorem request_bounds {bits available : Nat} (hbits : 512 ≤ bits)
    (hroom : available < parameterEntropy bits) :
    available < parameterRequest bits available ∧ parameterRequest bits available ≤ parameterEntropy bits := by
  unfold parameterRequest
  have hlen : 0 < (bits + 7) / 8 := by omega_using [hbits]
  have hmax₁ := Nat.le_max_left available (256 * ((bits + 7) / 8))
  have hmax₂ := Nat.le_max_right available (256 * ((bits + 7) / 8))
  refine ⟨Nat.lt_min.mpr ⟨?_, hroom⟩, Nat.min_le_right _ _⟩
  omega_using [hmax₁, hmax₂, hlen]

theorem candidate_rest {bits generator : Nat} {rand rest : Rand} {value : Option Nat}
    (h : parameterCandidate bits generator rand = some (value, rest)) :
    rest = rand.drop (rand.length - rest.length) := by
  obtain ⟨used, hu, hr⟩ := candidate_suffix h
  have hl : rand.length - rest.length = used := by
    rw [hr, List.length_drop]
    omega_using [hu]
  rw [hl]
  exact hr

theorem search_reject {bits generator remaining used : Nat} {rand rest : Rand}
    (hr : 0 < remaining)
    (hc : parameterCandidate bits generator (rand.drop used) = some (none, rest)) :
    (parameterSearch bits generator remaining (rand.drop used)).consume used =
      (parameterSearch bits generator (remaining - 1)
        (rand.drop (used + ((rand.drop used).length - rest.length)))).consume
        (used + ((rand.drop used).length - rest.length)) := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    rw [parameterSearch, hc, consume_assoc, Nat.add_sub_cancel]
    have he : rest = rand.drop (used + ((rand.drop used).length - rest.length)) :=
      (candidate_rest hc).trans List.drop_drop
    exact congrArg (fun r => (parameterSearch bits generator n r).consume
      (used + ((rand.drop used).length - rest.length))) he

end VG.Proof.Ffdh.Generation
