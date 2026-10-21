module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateMain
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest

/-! Short entropy returns and the full native candidate body share the public tape-length guard. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CandidateRoomEnd (p : CandidatePoint) (s : State) : Prop :=
  CandidateContextStart p s ∧ s.z = decide (p.params.bytes.length < p.params.length)

private theorem candidateRoomEnd_ok (p : CandidatePoint) (s : State) (h : CandidateContextStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) s (CandidateRoomEnd p) := by
  refine WP.mono (initialRoom_ok h.saved.space p.params.tapeCount
    (by have := p.params.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.after_memory mem rest, zero⟩

theorem candidateGuard_ct (v : RoundImpl) : RelCT isa (Two CandidateContextStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)])
    (fun _ _ => True) := by
  have room : RelCT isa (Two CandidateContextStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) (Two CandidateRoomEnd) :=
    two_post (initialRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateRoomEnd_ok
  have branch : RelCT isa (Two CandidateRoomEnd)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code))
      (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.2, right.2]
    · exact two_map id (fun _ _ h => h.1.1) candidateNone_ct
    · refine two_map id ?_ (candidateMain_ct v)
      intro p s h
      have enough : p.params.length ≤ p.params.bytes.length := by
        have go := h.2
        change some s.z = some false at go
        rw [h.1.2] at go
        have := of_decide_eq_false (Option.some.inj go)
        omega
      exact ⟨h.1.1, enough⟩
  exact room.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
