module

public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RSA key generation: the shape of a candidate

An accepted candidate of `bits` bits is odd, below `2^bits`, with its two
most significant bits set (`PrimeShape`), as every `candidate` is
(`candidate_shape`). What every result of an iteration that finishes
satisfies, the loop's result satisfies (`loop_inl`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec
open VG.Spec.RsaKeyGen

/-- An accepted candidate of `bits` bits: odd, below `2^bits`, with its two
most significant bits set. -/
def PrimeShape (bits c : Nat) : Prop := c % 2 = 1 ∧ 3 * 2 ^ (bits - 2) ≤ c ∧ c < 2 ^ bits

/-! ## Loops -/

/-- What every result of an iteration that finishes satisfies, the loop's
result satisfies. -/
theorem loop_inl {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)} (P : α → Prop)
    (hstep : ∀ s r a r', step s r = some (.inl a, r') → P a) :
    ∀ s r a r', loop step s r = some (a, r') → P a := by
  intro s r
  induction r using (measure List.length).wf.induction generalizing s with
  | h r ih =>
    intro a r' h
    rw [loop] at h
    split at h
    · cases h
    · cases h
      exact hstep _ _ _ _ (by assumption)
    · split at h
      · exact ih _ (by assumption) _ _ _ h
      · cases h

/-! ## Candidates -/

theorem candidate_shape {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    PrimeShape bits (candidate bits x) := by
  unfold candidate PrimeShape
  have h4 : 2 ^ bits = 2 ^ (bits - 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
  have hpos := Nat.two_pow_pos (bits - 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.or_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one ((x % 2 ^ bits ||| 3 * 2 ^ (bits - 2))) with h | h <;>
      simp [h]
  · exact Nat.le_trans (Nat.right_le_or) (Nat.left_le_or)
  · exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega))
      (Nat.one_lt_two_pow (by omega))




end VG.Proof.RsaKeyGen
