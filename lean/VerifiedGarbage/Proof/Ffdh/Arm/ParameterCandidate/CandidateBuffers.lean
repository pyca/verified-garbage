module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateDimensions`, which this module and modules that import it used -/

section

/-! The existing FFDH allocation fits both RSA arithmetic and the compact prime table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

theorem CandidateParams.length_bounds (p : CandidateParams) : 64 ≤ p.length ∧ p.length ≤ 1024 := by
  have := p.minBits
  have := p.maxBits
  dsimp only [CandidateParams.length]
  omega_arith

theorem CandidateParams.public_space (p : CandidateParams) : Spec.Rsa.publicScratchWords p.length ≤ p.capacity := by
  have := p.length_bounds
  have space : 16 * p.length + 32 ≤ p.capacity := p.space
  dsimp only [Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords]
  omega_using [this, space]

theorem CandidateParams.table_fits (p : CandidateParams) : Proof.Rsa.Mont.arrAt p.words 34 + 4096 ≤ 8 * p.capacity := by
  have := p.length_bounds
  have space : 16 * p.length + 32 ≤ p.capacity := p.space
  dsimp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, CandidateParams.words, Spec.Rsa.modulusWords]
  omega_using [this, space]

theorem CandidateParams.capacity_fits (p : CandidateParams) : p.capacity < 2 ^ 32 := by
  have := p.scratchFits
  omega_using [this]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Bind candidate buffers and saved arguments to the existing native helper contracts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem CandidateContext.mask {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : MaskCtx s p.out p.length :=
  maskCtx_of_region s (by have := p.length_bounds; omega_using [this]) p.outputFits h.outputWrite

theorem CandidateContext.output_read {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : InRegions (s.rd ++ s.wr) (State.addr p.out) p.length := by
  obtain ⟨r, hr, contains⟩ := h.outputWrite
  exact ⟨r, List.mem_append_right _ hr, contains⟩

theorem CandidateContext.read_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : ReadContext p.out p.length s := by
  refine ⟨h.saved.project ?_ ?_, by have := p.length_bounds; omega_using [this],
    by have := p.length_bounds; omega_using [this], p.outputFits, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  · intro i hi
    rw [VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_using [hi] : i + 1 ≤ p.length)]
    exact h.mask.readable (p.length - (i + 1)) (by omega_using [hi])

theorem CandidateContext.result_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : ResultContext p.out p.usedPtr p.length consumed s := by
  refine ⟨h.saved.project ?_ ?_, ⟨p.outputFits, h.outputWrite⟩, ⟨p.usedFits, h.usedWrite⟩,
    by have := p.length_bounds; omega_using [this], by have := p.length_bounds; omega_using [this],
    by have := h.consumedBound; have := p.tapeCount; omega_arith,
    h.stackOutput.symm, h.stackUsed.symm, p.outputUsed⟩
  · intro d hd
    simp only [resultSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    simp only [resultSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
