module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateSieve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! Halve p, screen q, then enter native rounds only when its public sieve passes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenQStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  table : TableData p.base p.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private structure QHalved (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  table : TableData p.base p.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2
  zero : s.z = decide (((p.candidate - 1) / 2) % 2 = 0)

private theorem qHalved_ok (p : CandidateParams) (s : State) (h : ScreenQStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s (QHalved p) := by
  refine WP.mono (candidateHalve_ok h.context h.table h.number) ?_
  rintro t ⟨ctx, table, number, zero, _, _⟩
  exact ⟨ctx, h.enough, table, number, zero⟩

private def QSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidateSieveStart true ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def QSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidateSieved true ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem qSieve_ct (v : RoundImpl) : RelCT isa (Two QSieveStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.sieve,
      .ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]) (fun _ _ => True) := by
  have sieve : RelCT isa (Two QSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (Two QSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidateSieve_ct true)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidateSieved_ok true _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two QSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint))
        (fun _ _ h => ⟨⟨h.1.1.start.context, h.1.1.start.number, h.1.1.start.odd⟩, h.1.2⟩) (candidateTests_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint))
        (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

theorem candidateScreenQ_ct (v : RoundImpl) : RelCT isa (Two ScreenQStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ v.name v.code) (fun _ _ => True) := by
  have halve : RelCT isa (Two ScreenQStart) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (Two QHalved) :=
    two_post (two_map (fun p => (p.out, p.length)) (fun _ _ h => h.context.read_context) halveQ_ct) qHalved_ok
  have branch : RelCT isa (Two QHalved)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected
        (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.sieve,
          .ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
            VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected])) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.context) candidateRejected_ct
    · refine two_map id ?_ (qSieve_ct v)
      intro p s h
      have odd : ((p.candidate - 1) / 2) % 2 = 1 := by
        have notEven : ¬ ((p.candidate - 1) / 2) % 2 = 0 := by
          have go := h.2
          change some s.z = some false at go
          rw [h.1.zero] at go
          exact of_decide_eq_false (Option.some.inj go)
        omega
      exact ⟨⟨h.1.context, h.1.table, h.1.number, odd⟩, h.1.enough⟩
  exact halve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
