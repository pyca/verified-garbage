module

public import VerifiedGarbage.Impl.EcKey.Compressed.Root

/-! # Soundness and completeness of checked root recovery

The machine-code proofs use this interface without loading finite-field
algebra. Each curve supplies square-root completeness and the fact that
two square roots differ only by sign. Neither is a trusted assumption:
the field proofs establish them in the curve variants.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed

open VG.Impl.EcKey.Compressed

variable {p : Nat} [NeZero p]

/-- The two mathematical facts needed from a curve's square-root method. -/
structure RootFacts (root : Fin p → Fin p) : Prop where
  complete : ∀ a, (∃ y : Fin p, y * y = a) → root a * root a = a
  unique : ∀ {x y : Fin p}, x * x = y * y → x = y ∨ x = -y

omit [NeZero p] in
/-- Acceptance is exactly a root with the requested canonical parity. -/
theorem recoverRoot_some {root : Fin p → Fin p} {a y : Fin p} {b : Nat}
    (h : recoverRoot root a b = some y) : y * y = a ∧ y.val % 2 = b := by
  simp only [recoverRoot] at h
  split at h <;> split at h
  all_goals first | (cases h; assumption) | contradiction

/-- Every representable root parity is accepted; an odd zero is not
silently mapped to an even root. -/
theorem recoverRoot_complete {root : Fin p → Fin p} (hf : RootFacts root)
    {a : Fin p} {b : Nat} (ha : ∃ y : Fin p, y * y = a ∧ y.val % 2 = b) :
    ∃ y, recoverRoot root a b = some y := by
  obtain ⟨y, hsq, hpar⟩ := ha
  have hr := hf.complete a ⟨y, hsq⟩
  have hneg : -(root a) * -(root a) = a := by
    calc
      -(root a) * -(root a) = root a * root a := by grind
      _ = a := hr
  have hp : (root a).val % 2 = b ∨ (-(root a)).val % 2 = b := by
    rcases hf.unique (hsq.trans hr.symm) with h | h
    · exact Or.inl (h ▸ hpar)
    · exact Or.inr (h ▸ hpar)
  simp only [recoverRoot]
  split
  · exact ⟨root a, ite_eq_left ⟨hr, by assumption⟩⟩
  · exact ⟨-(root a), ite_eq_left ⟨hneg, hp.resolve_left (by assumption)⟩⟩

/-- Rejection certifies that no root of the requested parity exists. -/
theorem recoverRoot_none_iff {root : Fin p → Fin p} (hf : RootFacts root)
    (a : Fin p) (b : Nat) :
    recoverRoot root a b = none ↔ ¬ ∃ y : Fin p, y * y = a ∧ y.val % 2 = b := by
  constructor
  · intro h he
    obtain ⟨y, hy⟩ := recoverRoot_complete hf he
    rw [h] at hy
    contradiction
  · intro h
    cases he : recoverRoot root a b with
    | none => rfl
    | some y => exact False.elim (h ⟨y, recoverRoot_some he⟩)

end VG.Proof.EcKey.Compressed
