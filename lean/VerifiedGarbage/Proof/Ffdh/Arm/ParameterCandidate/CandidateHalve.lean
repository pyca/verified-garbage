module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.HalveQ
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Divide the shaped p into q in place without disturbing the RSA sieve table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (arrAt)

private theorem table_after_output {s t : State} {p : CandidateParams}
    (table : TableData p.base p.length s.mem) (changed : Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem) :
    TableData p.base p.length t.mem := by
  intro i hi
  have fit : arrAt ((p.length + 7) / 8) 34 + 4096 ≤ 8 * p.capacity := p.table_fits
  have equal := changed.readW (a := off (State.addr p.base) (arrAt ((p.length + 7) / 8) 34 + 4 * i)) (w := 32)
    (r := ⟨State.addr p.base, 8 * p.capacity⟩)
    (Offset.contains_base _ (by omega) (by have := p.scratchFits; omega)) (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact p.outputScratch.symm) (by decide)
  exact (congrArg BitVec.toNat equal).trans (table i hi)

theorem candidateHalveValue_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      CandidateContext p consumed t ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 ∧
      t.z = decide (((p.candidate - 1) / 2) % 2 = 0) ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let bs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have size : bs.length = p.length := by simp [bs, Spec.Rsa.bytesAt]
  have saved : SavedFrame (readValues p.out bs.length) [4, 12] s := by rw [size]; exact h.read_context.frame
  have mask : MaskCtx s p.out bs.length := by rw [size]; exact h.mask
  have bytes : ∀ j < bs.length, s.mem (State.addr (p.out + BitVec.ofNat 32 j)) = bs[j]?.getD 0 := by
    intro j hj
    have bound : j < p.length := by rwa [size] at hj
    rw [VG.Arm.addr_add (by have fit : p.out.toNat + p.length ≤ 2 ^ 32 := p.outputFits; omega)]
    simp only [bs, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range bound, Option.map_some, Option.getD_some]
  refine WP.mono (halveQ_ok saved mask (by rw [size]; have := p.length_bounds; omega)
    (by rw [size]; exact p.outputFits) bytes) ?_
  rintro t ⟨_, value, zero, changed, rest⟩
  rw [size] at value changed
  have source : Spec.Rsa.os2ip bs = p.candidate := number
  have half : p.candidate / 2 = (p.candidate - 1) / 2 := by have := p.candidate_odd; omega
  rw [source, half] at value zero
  exact ⟨h.after_output changed rest, value, zero, changed,
    rest.mono (by simp [roundClobbers])⟩


theorem candidateHalve_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 ∧
      t.z = decide (((p.candidate - 1) / 2) % 2 = 0) ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (candidateHalveValue_ok h number) ?_
  rintro t ⟨context, value, zero, changed, rest⟩
  exact ⟨context, table_after_output table changed, value, zero, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
