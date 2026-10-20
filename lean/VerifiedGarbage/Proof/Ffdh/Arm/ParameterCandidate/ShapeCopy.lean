module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeCopyHead
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Framework.Omega

/-! Reuse RSA's verified disjoint-buffer copy for the candidate tape prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem shapeCopy_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy s fun t =>
      ShapeContext dst src bs bits t ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy
  refine WP.seq (WP.mono (shapeCopyHead_ok s h) ?_)
  rintro u ⟨⟨dest, source, count, memory⟩, rest⟩
  have context := h.after_memory memory rest
  refine WP.mono (copyBytes_ok u
    (copyCtx_of_regions u src dst (by have := h.size; omega) h.sourceFits h.destFits
      context.read context.write h.buffers)
    (by have := h.size; omega) source dest count) ?_
  intro t copied
  have frame := copied.frame h.destFits
  refine ⟨context.after_output frame copied.rest, ?_, ?_, (rest.mono (by simp)).trans copied.rest⟩
  · intro i hi
    rw [copied.copied i hi, memory]
    exact h.byte hi
  · rw [memory] at frame
    exact frame

end VG.Proof.Ffdh.Arm.ParameterCandidate
