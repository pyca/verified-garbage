module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Instantiate the shared RSA phase contract from candidate API bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

private theorem CandidateContext.pc_stack {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) :
    PcStack p.base (s.mem.readW (off (State.addr s.sp) 4) 32) p.out p.capacity p.length s := by
  refine ⟨by have := h.saved.space.nowrap; omega, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · refine ⟨_, List.mem_append_right _ h.saved.space.writable, ?_⟩
    simpa only [BitVec.add_zero, candidateValues] using
      Offset.contains_base (State.addr s.sp) (d := 0) (n := 16) (k := 72) (by decide) (by decide)
  · exact h.stackScratch.sub_left (Region.sub_prefix (by decide : 16 ≤ 72))
  · simpa only [BitVec.add_zero, candidateValues] using h.saved.saved 0 (by decide)
  · have word := h.saved.saved 8 (by decide)
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)] at word
    exact word
  · have word := h.saved.saved 12 (by decide)
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)] at word
    exact word

theorem candidatePhaseInput {s : State} {p : CandidateParams} {consumed : Nat} {q : Bool}
    (h : CandidateContext p consumed s)
    (saved : SavedFrame (witnessValues (candidatePhase p q) consumed 0) witnessSlots s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (candidatePhase p q).modulus)
    (odd : (candidatePhase p q).modulus % 2 = 1) :
    PhaseInput (candidatePhase p q) p.out p.length consumed s := by
  obtain ⟨positive, bound, fit, checksPositive, checksBound⟩ := p.phase_bounds q
  refine ⟨?_, saved, rfl, number, p.space, h.stackScratch, h.stackBelow, h.belowScratch,
    p.phase_bits_exact q odd, positive, bound, fit, checksPositive, checksBound, h.consumedBound,
    p.tapeCount, p.tapeFits, h.tapeRead, p.tapeScratch, h.stackTape.symm, h.belowTape.symm, h.tapeBytes⟩
  refine ⟨h.workspace, h.pc_stack, p.length_bounds.1, p.length_bounds.2, p.public_space,
    p.outputFits, h.output_read, p.outputScratch, ?_, ?_⟩
  · rw [number]
    exact p.phase_large q
  · rw [number]
    exact odd

end VG.Proof.Ffdh.Arm.ParameterCandidate
