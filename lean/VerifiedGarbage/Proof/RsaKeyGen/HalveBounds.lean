module

public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-! # Common halving never increases either factor or the product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem halveStep_bounds {st : Nat × Nat × Nat} {a b f : Nat}
    (h : st.1 < a ∧ st.2.1 < b ∧ st.2.2 < f) :
    (halveStep st).1 < a ∧ (halveStep st).2.1 < b ∧ (halveStep st).2.2 < f := by
  unfold halveStep
  split
  · exact ⟨Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h.1,
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h.2.1,
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h.2.2⟩
  · exact h

theorem halveIter_bounds (k : Nat) {st : Nat × Nat × Nat} {a b f : Nat}
    (h : st.1 < a ∧ st.2.1 < b ∧ st.2.2 < f) :
    (halveIter k st).1 < a ∧ (halveIter k st).2.1 < b ∧ (halveIter k st).2.2 < f := by
  induction k generalizing st with
  | zero => exact h
  | succ k ih => exact ih (halveStep_bounds h)

end VG.Proof.RsaKeyGen
