module

public import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # The number of halvings is bounded by the public iteration count -/

@[expose] public section
namespace VG.Proof.Rsa

theorem halve_count_le (m k : Nat) : (halveStep^[k] (m, 0)).2 ≤ k := by
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    generalize halveStep^[k] (m, 0) = st at ih ⊢
    unfold halveStep
    split
    · show st.2 + 1 ≤ k + 1; omega
    · show st.2 ≤ k + 1; omega

end VG.Proof.Rsa
