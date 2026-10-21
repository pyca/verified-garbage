module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntered
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Preserve the AAPCS callee-saved registers around complete candidate generation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidateFnInput (p : CandidateParams) (s : State) : Prop where
  stackFits : 184 ≤ s.sp.toNat
  start : CandidateStart p (entered s)
  incoming : CandidateIncoming p (entered s)
  out : (entered s).gpr .r0 = p.out
  width : (entered s).gpr .r1 = BitVec.ofNat 32 p.length
  used : (entered s).gpr .r2 = p.usedPtr
  bits : (entered s).gpr .r3 = BitVec.ofNat 32 p.bits
  saved : ∀ r ∈ candidateEnteredRegions p (entered s).sp,
    (⟨State.addr (VG.Proof.Bignum.Arm.pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem candidateFn_ok (v : RoundImpl) {s : State} {p : CandidateParams} (h : CandidateFnInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) s fun t =>
      abiPreserved s t ∧ candidatePost p t.mem (t.gpr .r0) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.code
  exact framed_of_separate _ s (by have := h.stackFits; omega)
    (candidateEnteredRegions p (entered s).sp) (candidatePost p) h.saved
    (candidateEntered_ok v h.start h.incoming h.out h.width h.used h.bits)

end VG.Proof.Ffdh.Arm.ParameterCandidate
