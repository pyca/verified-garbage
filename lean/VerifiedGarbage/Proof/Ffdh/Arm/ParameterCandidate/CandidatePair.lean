module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairSieve
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidatePair_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate)
    (oddQ : ((p.candidate-1)/2)%2=1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      t.z=((Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) &&
        (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2))) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
      Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (pair_shape_ok (h.sieve_context table) (bits:=p.bits) rfl
    (by rw [number]; exact p.sieve_large.1) (by rw [number]; exact p.sieve_large.2)
    (by rw [number]; exact p.candidate_odd) (by rw [number]; exact oddQ)) ?_
  rintro t ⟨ctx, flag, changed, rest⟩
  rw [number] at flag
  have frame : Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem := changed
  refine ⟨h.after_aux (by decide : 44 ≤ 64) (by decide : 64 + 4 ≤ 68) frame rest,
    ctx.table, flag, ?_, frame, rest.mono (by simp [sieveRegs, roundClobbers])⟩
  refine rsa_bytes_frame frame (by have := p.length_bounds; omega) ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
  exact h.stackOutput.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate
