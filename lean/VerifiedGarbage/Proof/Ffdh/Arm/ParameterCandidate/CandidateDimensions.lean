module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.Omega

/-! The existing FFDH allocation fits both RSA arithmetic and the compact prime table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

theorem CandidateParams.length_bounds (p : CandidateParams) : 64 ≤ p.length ∧ p.length ≤ 1024 := by
  have := p.minBits
  have := p.maxBits
  dsimp only [CandidateParams.length]
  omega

theorem CandidateParams.words_bounds (p : CandidateParams) : 8 ≤ p.words ∧ p.words ≤ 128 := by
  have := p.length_bounds
  dsimp only [CandidateParams.words, Spec.Rsa.modulusWords]
  omega

theorem CandidateParams.public_space (p : CandidateParams) : Spec.Rsa.publicScratchWords p.length ≤ p.capacity := by
  have := p.length_bounds
  have space : 16 * p.length + 32 ≤ p.capacity := p.space
  dsimp only [Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords]
  omega

theorem CandidateParams.table_fits (p : CandidateParams) : Proof.Rsa.Mont.arrAt p.words 34 + 4096 ≤ 8 * p.capacity := by
  have := p.length_bounds
  have space : 16 * p.length + 32 ≤ p.capacity := p.space
  dsimp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, CandidateParams.words, Spec.Rsa.modulusWords]
  omega

theorem CandidateParams.capacity_fits (p : CandidateParams) : p.capacity < 2 ^ 32 := by
  have := p.scratchFits
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
