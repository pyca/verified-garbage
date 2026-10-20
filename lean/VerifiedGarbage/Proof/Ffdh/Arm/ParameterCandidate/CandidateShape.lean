module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega

/-! Candidate shaping draws exactly the first p-width bytes of the original tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

theorem CandidateContext.shape_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (enough : p.length ≤ p.bytes.length) :
    ShapeContext p.out p.tape (p.bytes.take p.length) p.bits s := by
  have size : (p.bytes.take p.length).length = p.length := by rw [List.length_take, Nat.min_eq_left enough]
  refine ⟨h.saved.project ?_ ?_, by have := p.minBits; omega, p.maxBits, size, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [shapeSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    rw [size]
    simp only [shapeSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl
  · rw [size]
    have := p.tapeFits
    omega
  · rw [size]
    exact p.outputFits
  · rw [size]
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub h.tapeRead
      (off := 0) (by omega : 0 + p.length ≤ p.bytes.length) (by have := p.tapeCount; omega)
  · rw [size]
    exact h.outputWrite
  · rw [size]
    exact p.outputTape.symm.sub_left (Region.sub_prefix enough)
  · rw [size]
    exact h.stackOutput.symm
  · rw [size]
    have slice := VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.tape)
      (offset := 0) (len := p.length) (by omega : 0 + p.length ≤ p.bytes.length)
    simpa only [List.drop_zero, BitVec.add_zero, h.tapeBytes] using slice.symm

theorem candidateShape_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (enough : p.length ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP s fun t =>
      CandidateContext p consumed t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
        shapedOctets (p.bytes.take p.length) ((p.bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = p.candidate ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (shapeP_ok s (h.shape_context enough)) ?_
  rintro t ⟨_, bytes, value, changed, rest⟩
  have size : (p.bytes.take p.length).length = p.length := by rw [List.length_take, Nat.min_eq_left enough]
  rw [size] at bytes value changed
  exact ⟨h.after_output changed rest, bytes, value, changed, rest.mono (by simp [roundClobbers])⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
