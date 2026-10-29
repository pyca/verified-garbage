module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeMasks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeTop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeOdd
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! Candidate shaping draws exactly the first p-width bytes of the original tape. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Shape.lean`, which only this module imported.
section

/-! Complete native shaping of the first candidate drawn from the tape. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.ParameterCandidate (topCut topCut_length lastOne_length shapedOctets shapedOctets_value)

private def shapeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .lr]

theorem shapeP_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP s fun t =>
      ShapeContext dst src bs bits t ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = shapedOctets bs ((bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length) =
        VG.Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip bs) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .lr] s t := by
  have size := h.size
  have nonempty : bs ≠ [] := by intro nil; simp only [nil, List.length_nil] at size; omega
  have bitBound := Nat.mod_lt (bits - 1) (by decide : 0 < 8)
  have cutLength := topCut_length nonempty ((bits - 1) % 8)
  have cutNonempty : topCut bs ((bits - 1) % 8) ≠ [] := by simp [topCut]
  have shapedLength : (shapedOctets bs ((bits - 1) % 8)).length = bs.length :=
    (lastOne_length cutNonempty).trans cutLength
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (shapeCopy_ok s h) ?_)
  rintro u ⟨contextU, copied, frameU, restU⟩
  refine WP.seq (WP.mono (shapeMasks_ok u (by have := h.minBits; omega) (by have := h.maxBits; omega)
    (contextU.frame.read (d := 24) (by decide)) (contextU.frame.saved 24 (by decide))) ?_)
  rintro v ⟨mask, memory, restV⟩
  have contextV := contextU.after_memory memory restV
  have bytesV : ∀ i < bs.length, v.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0 := by
    intro i hi
    rw [memory]
    exact copied i hi
  refine WP.seq (WP.mono (shapeTop_ok v contextV bitBound bytesV mask) ?_)
  rintro w ⟨contextW, destW, bytesW, frameW, restW⟩
  refine WP.seq (WP.mono (shapeOdd_ok w contextW cutLength (by
    intro i hi
    simpa only [List.getD_eq_getElem?_getD] using bytesW i hi) destW) ?_)
  rintro t ⟨contextT, bytesT, frameT, restT⟩
  have encoding : Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = shapedOctets bs ((bits - 1) % 8) := by
    apply List.ext_getElem
    · rw [VG.Proof.Bignum.bytesAt_length]
      exact shapedLength.symm
    · intro i hi hi'
      have bound : i < bs.length := by rwa [VG.Proof.Bignum.bytesAt_length] at hi
      have byte := bytesT i bound
      rw [VG.Arm.addr_add (by have := h.destFits; omega)] at byte
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (State.addr dst + BitVec.ofNat 64 i) =
        (shapedOctets bs ((bits - 1) % 8)).getD i 0 at byte
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi', Option.getD_some] using byte
  have frameV : Frame [⟨State.addr dst, bs.length⟩] s.mem v.mem := by
    rw [memory]
    exact frameU
  have restUV : Rest shapeRegs s v := (restU.mono (by simp [shapeRegs])).trans (restV.mono (by simp [shapeRegs]))
  have restUW : Rest shapeRegs s w := restUV.trans (restW.mono (by simp [shapeRegs]))
  refine WP.block_nil ⟨contextT, encoding, ?_, (frameV.trans frameW).trans frameT,
    restUW.trans (restT.mono (by simp [shapeRegs]))⟩
  rw [encoding, shapedOctets_value (bits := bits) (j := (bits - 1) % 8) nonempty bitBound (by have := h.length; have := h.minBits; omega)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

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
