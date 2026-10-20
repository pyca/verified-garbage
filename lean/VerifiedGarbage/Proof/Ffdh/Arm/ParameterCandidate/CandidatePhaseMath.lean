module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! q and p share the fixed p-width RSA workspace and the same entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidatePhase (p : CandidateParams) (q : Bool) : WitnessParams where
  base := p.base
  tape := p.tape
  capacity := p.capacity
  words := p.words
  modulus := if q then (p.candidate - 1) / 2 else p.candidate
  bits := phaseBits q p.bits
  checks := Spec.Ffdh.primeChecks (phaseBits q p.bits)
  bytes := p.bytes

theorem CandidateParams.phase_large (p : CandidateParams) (q : Bool) : 1 < (candidatePhase p q).modulus := by
  obtain ⟨odd, lower, upper⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by have := p.minBits; omega : 2 ≤ p.bits) (Spec.Rsa.os2ip (p.bytes.take p.length))
  obtain ⟨halfLower, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by have := p.minBits; omega) odd lower upper
  have lowP : 2 ^ 2 ≤ 2 ^ (p.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega)
  have lowQ : 2 ^ 2 ≤ 2 ^ (p.bits - 2) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega)
  change 1 < if q then (p.candidate - 1) / 2 else p.candidate
  change 2 ^ (p.bits - 1) ≤ p.candidate at lower
  change 2 ^ (p.bits - 2) ≤ (p.candidate - 1) / 2 at halfLower
  change 4 ≤ 2 ^ (p.bits - 1) at lowP
  change 4 ≤ 2 ^ (p.bits - 2) at lowQ
  cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem CandidateParams.phase_bits_exact (p : CandidateParams) (q : Bool)
    (odd : (candidatePhase p q).modulus % 2 = 1) :
    (candidatePhase p q).bits = Spec.RsaKeyGen.bitLength ((candidatePhase p q).modulus - 1) := by
  cases q
  · exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits)
      (by have := p.minBits; omega) (Spec.Rsa.os2ip (p.bytes.take p.length))).2.symm
  · exact (VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits)
      (by have := p.minBits; omega) (Spec.Rsa.os2ip (p.bytes.take p.length)) odd).symm

theorem CandidateParams.phase_bounds (p : CandidateParams) (q : Bool) :
    0 < (candidatePhase p q).bits ∧ (candidatePhase p q).bits ≤ 8192 ∧
    (candidatePhase p q).bits ≤ 64 * p.words ∧
    0 < (candidatePhase p q).checks ∧ (candidatePhase p q).checks ≤ 128 := by
  have low := p.minBits
  have high := p.maxBits
  have bitsFit : p.bits ≤ 64 * p.words := by
    dsimp only [CandidateParams.words, CandidateParams.length, Spec.Rsa.modulusWords]
    omega
  have phaseFit : phaseBits q p.bits ≤ p.bits := by cases q <;> simp [phaseBits]
  have phasePositive : 0 < phaseBits q p.bits := by cases q <;> simp [phaseBits] <;> omega
  have count : 0 < Spec.Ffdh.primeChecks (phaseBits q p.bits) ∧
      Spec.Ffdh.primeChecks (phaseBits q p.bits) ≤ 128 := by
    unfold Spec.Ffdh.primeChecks
    split <;> decide
  exact ⟨phasePositive, by change phaseBits q p.bits ≤ 8192; omega,
    by change phaseBits q p.bits ≤ 64 * p.words; omega, count⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
