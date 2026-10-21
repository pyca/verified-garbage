module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedQ
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLimitedTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLimitedResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest

/-! Early p screening follows public primality results and exact entropy suffixes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def ScreenedFirstStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateTestStart false p s ∧ p.params.length ≤ p.params.bytes.length ∧ ((p.params.candidate - 1) / 2) % 2 = 1

private def qAnswer (p : CandidatePoint) : Option (Bool × List Byte) :=
  witnessRemaining (limitedPhase p.params true) p.used 0

private structure CandidateFirstReady (p : CandidatePoint) (s : State) : Prop where
  enough : p.params.length ≤ p.params.bytes.length
  odd : ((p.params.candidate - 1) / 2) % 2 = 1
  context : ∃ next, CandidateContext p.params next s ∧
    ∀ pass tail, qAnswer p = some (pass, tail) → tail = p.params.bytes.drop next
  status : s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (qAnswer p))
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = p.params.candidate

private theorem candidateFirstReady_ok (v : RoundImpl) (p : CandidatePoint) (s : State) (h : ScreenedFirstStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited true v.name v.code) s (CandidateFirstReady p) := by
  refine WP.mono (limitedTest_ok v (first := true) h.1.1 h.1.2.1 h.1.2.2) ?_
  rintro t ⟨next, ctx, _, status, suffix, bytes, _, _⟩
  exact ⟨h.2.1, h.2.2, ⟨next, ctx, suffix⟩, status, by rw [bytes]; exact h.1.2.1⟩

private structure CandidateFirstCompared (p : CandidatePoint) (s : State) : Prop where
  ready : CandidateFirstReady p s
  zero : s.z = decide (witnessResultStatus (qAnswer p) = 1)

private theorem candidateFirstCompare_ok (p : CandidatePoint) (s : State) (h : CandidateFirstReady p s) :
    WP isa (.block [.cmp .r3 (.imm 1)]) s (CandidateFirstCompared p) := by
  refine WP.mono (cmpStatus_ok _ 1 (by have := witnessResultStatus_bound (qAnswer p); omega) (by decide) h.status) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  obtain ⟨next, ctx, suffix⟩ := h.context
  exact ⟨⟨h.enough, h.odd, ⟨next, ctx.after_memory mem rest, suffix⟩,
    (rest.gpr .r3 (by simp)).trans h.status, by rw [mem]; exact h.number⟩, zero⟩

private def acceptedUsed (p : CandidatePoint) : Nat :=
  p.params.bytes.length - ((qAnswer p).map fun pair => pair.2.length).getD 0

private theorem acceptedContext (p : CandidatePoint) (s : State) (h : CandidateFirstCompared p s)
    (go : isa.eval .eq s = some true) : ScreenedQStart ⟨p.params, acceptedUsed p⟩ s := by
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
  exact ⟨by rw [same]; exact ctx, h.ready.enough, h.ready.number, h.ready.odd⟩

private theorem screenedFirst_ct (v : RoundImpl) : RelCT isa (Two ScreenedFirstStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited true v.name v.code, .block [.cmp .r3 (.imm 1)],
      .ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ v.name v.code) VG.Impl.Ffdh.Arm.ParameterCandidate.result]) (fun _ _ => True) := by
  have q : RelCT isa (Two ScreenedFirstStart)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited true v.name v.code) (Two CandidateFirstReady) :=
    two_post ((limitedTest_ct v true).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) (candidateFirstReady_ok v)
  have compare : RelCT isa (Two CandidateFirstReady) (.block [.cmp .r3 (.imm 1)]) (Two CandidateFirstCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateFirstCompare_ok
  have choice : RelCT isa (Two CandidateFirstCompared)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.result) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map (fun p => (⟨p.params, acceptedUsed p⟩ : CandidatePoint))
        (fun p s h => acceptedContext p s h.1 h.2) (screenedQ_ct v)
    · refine two_map id ?_ (candidateAnswerResult_ct (limitedAnswer true))
      intro p s h
      obtain ⟨next, ctx, _⟩ := h.1.ready.context
      exact ⟨⟨next, ctx⟩, h.1.ready.status⟩
  exact q.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

def ScreenedTestsStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧ p.params.length ≤ p.params.bytes.length ∧
    ((p.params.candidate - 1) / 2) % 2 = 1

theorem screenedTests_ct (v : RoundImpl) : RelCT isa (Two ScreenedTestsStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedTests v.name v.code) (fun _ _ => True) := by
  have shapeTrace : RelCT isa (Two ScreenedTestsStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.params.out, p.params.tape, p.params.bytes.take p.params.length, p.params.bits⟩ : ShapeData))
      (fun _ _ h => h.1.shape_context h.2.1) shapeP_ct
  have shape : RelCT isa (Two ScreenedTestsStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (Two ScreenedFirstStart) :=
    two_post shapeTrace (fun p _ h => WP.mono (candidateShape_ok h.1 h.2.1)
      (fun _ ⟨ctx, _, number, _, _⟩ => ⟨⟨ctx, number, p.params.candidate_odd⟩, h.2⟩))
  exact shape.seq (screenedFirst_ct v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
