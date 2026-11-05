module
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Proof.EntropyRequest

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

theorem consume_available (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).available = result.available := by
  cases result <;> rfl

theorem consume_assoc (result : ParameterSearchResult) (a b : Nat) :
    (result.consume b).consume a = result.consume (a + b) := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.add_assoc]

theorem consume_status (n : Nat) (result : ParameterSearchResult) :
    (result.consume n).status = result.status := by
  cases result <;> rfl

theorem consume_zero (result : ParameterSearchResult) : result.consume 0 = result := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.zero_add]

theorem request_bounds {bits available : Nat} (hbits : 512 ≤ bits)
    (hroom : available < parameterEntropy bits) :
    available < parameterRequest bits available ∧ parameterRequest bits available ≤ parameterEntropy bits := by
  unfold parameterRequest Entropy.request
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

end VG.Proof.Ffdh.Generation
