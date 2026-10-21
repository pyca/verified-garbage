module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! Both shaped moduli exceed every entry in the native shared RSA sieve. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

theorem CandidateParams.sieve_large (p : CandidateParams) :
    8161 < p.candidate ∧ 8161 < (p.candidate - 1) / 2 := by
  obtain ⟨odd, lower, upper⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by have := p.minBits; omega : 2 ≤ p.bits) (Spec.Rsa.os2ip (p.bytes.take p.length))
  obtain ⟨halfLower, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by have := p.minBits; omega) odd lower upper
  have lowP : 2 ^ 13 ≤ 2 ^ (p.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega)
  have lowQ : 2 ^ 13 ≤ 2 ^ (p.bits - 2) := Nat.pow_le_pow_right (by decide) (by have := p.minBits; omega)
  change 8192 ≤ 2 ^ (p.bits - 1) at lowP
  change 8192 ≤ 2 ^ (p.bits - 2) at lowQ
  change 2 ^ (p.bits - 1) ≤ p.candidate at lower
  change 2 ^ (p.bits - 2) ≤ (p.candidate - 1) / 2 at halfLower
  omega

theorem even_primeShape {n : Nat} (even : n % 2 = 0) : Spec.Ffdh.primeShape n = false := by
  simp [Spec.Ffdh.primeShape, even]

end VG.Proof.Ffdh.Arm.ParameterCandidate
