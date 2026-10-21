module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

/-! # Native candidate widths imply the shared prime shape and witness geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG

theorem candidate_shape {E : Environment} (v : E.Valid) (entropy : List Byte) :
    VG.Proof.RsaKeyGen.PrimeShape (64 * E.width) (candidateValue E entropy) := by
  have width := v.width_bounds.1
  have length := v.length_eq
  unfold candidateValue
  rw [show 8 * E.length = 64 * E.width by omega]
  exact VG.Proof.RsaKeyGen.candidate_shape (by omega) _

theorem candidate_odd {E : Environment} (v : E.Valid) (entropy : List Byte) :
    candidateValue E entropy % 2 = 1 := (candidate_shape v entropy).1

theorem candidate_large {E : Environment} (v : E.Valid) (entropy : List Byte) :
    8161 < candidateValue E entropy := by
  have width := v.width_bounds.1
  have shape := (candidate_shape v entropy).2.1
  have power : 2 ^ 12 ≤ 2 ^ (64 * E.width - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  change 3 * 2 ^ (64 * E.width - 2) ≤ candidateValue E entropy at shape
  omega

theorem candidate_bits {E : Environment} (v : E.Valid) (entropy : List Byte) :
    Spec.RsaKeyGen.bitLength (candidateValue E entropy) = 64 * E.width ∧
    Spec.RsaKeyGen.bitLength (candidateValue E entropy - 1) = 64 * E.width ∧
    Spec.RsaKeyGen.witnessBytes (candidateValue E entropy) = E.length := by
  have bits := VG.Proof.RsaKeyGen.cand_bits (by have := v.width_bounds.1; omega) (candidate_shape v entropy)
  rw [v.length_eq] at bits
  exact bits

end VG.Proof.RsaKeyGen.X86.Candidate
