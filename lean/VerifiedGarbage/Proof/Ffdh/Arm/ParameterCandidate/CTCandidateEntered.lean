module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateStart
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.EntryContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateGuard
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntry
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! Native entry snapshots the public candidate arguments before the complete controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidateEntryStart (p : CandidateParams) (s : State) : Prop where
  start : CandidateStart p s
  incoming : CandidateIncoming p s
  out : s.gpr .r0 = p.out
  width : s.gpr .r1 = BitVec.ofNat 32 p.length
  used : s.gpr .r2 = p.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.bits

private theorem candidateEntryStart_ok (p : CandidateParams) (s : State) (h : CandidateEntryStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) s (CandidateContextStart ⟨p, 0⟩) := by
  refine WP.mono (candidateEntry_ok h.start.locals h.incoming h.out h.width h.used h.bits) ?_
  rintro t ⟨saved, changed, rest⟩
  exact h.start.after_entry saved changed rest

theorem candidateEntered_ct (v : RoundImpl) : RelCT isa (Two CandidateEntryStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.entry,
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)])
    (fun _ _ => True) :=
  (two_post (candidateEntry_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateEntryStart_ok).seq
    ((candidateGuard_ct v).mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p, 0⟩, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
