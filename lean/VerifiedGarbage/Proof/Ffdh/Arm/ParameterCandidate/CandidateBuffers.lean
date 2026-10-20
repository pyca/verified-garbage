module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Framework.Omega

/-! Bind candidate buffers and saved arguments to the existing native helper contracts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem CandidateContext.mask {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : MaskCtx s p.out p.length :=
  maskCtx_of_region s (by have := p.length_bounds; omega) p.outputFits h.outputWrite

theorem CandidateContext.output_read {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : InRegions (s.rd ++ s.wr) (State.addr p.out) p.length := by
  obtain ⟨r, hr, contains⟩ := h.outputWrite
  exact ⟨r, List.mem_append_right _ hr, contains⟩

theorem CandidateContext.read_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : ReadContext p.out p.length s := by
  refine ⟨h.saved.project ?_ ?_, by have := p.length_bounds; omega,
    by have := p.length_bounds; omega, p.outputFits, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  · intro i hi
    rw [VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega : i + 1 ≤ p.length)]
    exact h.mask.readable (p.length - (i + 1)) (by omega)

theorem CandidateContext.result_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) : ResultContext p.out p.usedPtr p.length consumed s := by
  refine ⟨h.saved.project ?_ ?_, ⟨p.outputFits, h.outputWrite⟩, ⟨p.usedFits, h.usedWrite⟩,
    by have := p.length_bounds; omega, by have := p.length_bounds; omega,
    by have := h.consumedBound; have := p.tapeCount; omega,
    h.stackOutput.symm, h.stackUsed.symm, p.outputUsed⟩
  · intro d hd
    simp only [resultSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    simp only [resultSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
