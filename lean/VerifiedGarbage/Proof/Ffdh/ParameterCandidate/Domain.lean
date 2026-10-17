module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH shaped candidates give structurally valid PKCS #3 domains -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh

/-- Primality testing is independent of the algebraic checks for a domain without q. -/
theorem candidate_parametersValid {bits generator : Nat} (hlo : 512 ≤ bits) (hhi : bits ≤ 8192)
    (hg : generator = 2 ∨ generator = 5) (x : Nat) :
    parametersValid ⟨candidateOf bits x, generator, none⟩ = true := by
  obtain ⟨ho, hl, _⟩ := candidate_shape (bits := bits) (by omega) x
  have hbits := (candidate_bitLength (bits := bits) (by omega) x).1
  have hlarge : 16 ≤ candidateOf bits x := by
    have hpow : 2 ^ 4 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.le_trans hpow hl
  simp only [parametersValid, hbits, ho, beq_self_eq_true, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases hg with rfl | rfl <;> omega

end VG.Proof.Ffdh.ParameterCandidate
