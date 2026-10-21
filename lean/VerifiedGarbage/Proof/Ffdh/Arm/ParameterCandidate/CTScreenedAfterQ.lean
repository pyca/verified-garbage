module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLimitedFinal
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateResult

/-! The q batch and final p batch follow public primality results and entropy suffixes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def ScreenedAfterQStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateTestStart true p s ∧ p.params.length ≤ p.params.bytes.length

private def qAnswer (p : CandidatePoint) : Option (Bool × List Byte) :=
  witnessRemaining (candidatePhase p.params true) p.used 0

private structure CandidateQReady (p : CandidatePoint) (s : State) : Prop where
  enough : p.params.length ≤ p.params.bytes.length
  context : ∃ next, CandidateContext p.params next s ∧
    ∀ pass tail, qAnswer p = some (pass, tail) → tail = p.params.bytes.drop next
  status : s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (qAnswer p))

private theorem candidateQReady_ok (v : RoundImpl) (p : CandidatePoint) (s : State) (h : ScreenedAfterQStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.test true v.name v.code) s (CandidateQReady p) := by
  refine WP.mono (candidateTest_ok v h.1.1 h.1.2.1 h.1.2.2) ?_
  rintro t ⟨next, ctx, _, status, suffix, _, _, _⟩
  exact ⟨h.2, ⟨next, ctx, suffix⟩, status⟩

private structure CandidateQCompared (p : CandidatePoint) (s : State) : Prop where
  ready : CandidateQReady p s
  zero : s.z = decide (witnessResultStatus (qAnswer p) = 1)

private theorem candidateQCompare_ok (p : CandidatePoint) (s : State) (h : CandidateQReady p s) :
    WP isa (.block [.cmp .r3 (.imm 1)]) s (CandidateQCompared p) := by
  refine WP.mono (cmpStatus_ok _ 1 (by have := witnessResultStatus_bound (qAnswer p); omega) (by decide) h.status) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  obtain ⟨next, ctx, suffix⟩ := h.context
  exact ⟨⟨h.enough, ⟨next, ctx.after_memory mem rest, suffix⟩,
    (rest.gpr .r3 (by simp)).trans h.status⟩, zero⟩

private def acceptedUsed (p : CandidatePoint) : Nat :=
  p.params.bytes.length - ((qAnswer p).map fun pair => pair.2.length).getD 0

private theorem acceptedContext (p : CandidatePoint) (s : State) (h : CandidateQCompared p s)
    (go : isa.eval .eq s = some true) : LimitedFinalStart ⟨p.params, acceptedUsed p⟩ s := by
  have accepted : witnessResultStatus (qAnswer p) = 1 := by
    change some s.z = some true at go
    rw [h.zero] at go
    exact of_decide_eq_true (Option.some.inj go)
  obtain ⟨next, ctx, suffix⟩ := h.ready.context
  have same : acceptedUsed p = next := by
    cases answer : qAnswer p with
    | none => rw [answer] at accepted; change 0 = 1 at accepted; omega
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      cases pass with
      | false => rw [answer] at accepted; change 2 = 1 at accepted; omega
      | true =>
        have size := congrArg List.length (suffix true tail answer)
        rw [List.length_drop] at size
        simp only [acceptedUsed, answer, Option.map_some, Option.getD_some]
        have := ctx.consumedBound
        omega
  exact ⟨by rw [same]; exact ctx, h.ready.enough⟩

theorem screenedAfterQ_ct (v : RoundImpl) : RelCT isa (Two ScreenedAfterQStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ v.name v.code) (fun _ _ => True) := by
  have q : RelCT isa (Two ScreenedAfterQStart)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.test true v.name v.code) (Two CandidateQReady) :=
    two_post ((candidateTest_ct v true).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) (candidateQReady_ok v)
  have compare : RelCT isa (Two CandidateQReady) (.block [.cmp .r3 (.imm 1)]) (Two CandidateQCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateQCompare_ok
  have choice : RelCT isa (Two CandidateQCompared)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.result) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map (fun p => (⟨p.params, acceptedUsed p⟩ : CandidatePoint))
        (fun p s h => acceptedContext p s h.1 h.2) (limitedFinal_ct v)
    · refine two_map id ?_ (candidatePhaseResult_ct true)
      intro p s h
      obtain ⟨next, ctx, _⟩ := h.1.ready.context
      exact ⟨⟨next, ctx⟩, h.1.ready.status⟩
  exact q.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
