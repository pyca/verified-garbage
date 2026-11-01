module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLeaf
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTRequest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CandidateFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CompareResult
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-! Candidate classification and entropy exhaustion branch only on the public tape and policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_piece two_ite)

def EntropyCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧
  isa.eval .eq s = some (decide (q.inputs.c.bytes.length - q.used < Spec.Ffdh.parameterEntropy q.inputs.c.bits))

private theorem entropy_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s (EntropyCT q) := by
  refine WP.mono h.entropy_guard ?_
  rintro t ⟨⟨live, flag, _⟩, _⟩
  exact ⟨live, by change some t.z = _; rw [flag]⟩

theorem short_ct : RelCT isa (Two LiveCT) VG.Impl.Ffdh.Arm.ParameterSearch.short (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.short
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) entropy_ready) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact request_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)
  · exact exhausted_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
      ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1⟩, ⟨q.used, q.remaining, ht.1.1⟩, sp⟩) (fun _ _ h => h)

def PostCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧ CandidatePost q.inputs q.used s

def ComparisonCT (test : Nat) (q : SearchPoint) (s : State) : Prop := PostCT q s ∧
  isa.eval .eq s = some (decide (Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used) = test))

private theorem compare_ready (test : Nat) (which : test = 1 ∨ test = 2)
    (q : SearchPoint) (s : State) (h : PostCT q s) :
    WP isa (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) s (ComparisonCT test q) := by
  have small : Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used) < 3 := by
    cases candidateResult q.inputs q.used with
    | none => decide
    | some pair => obtain ⟨prime, rand⟩ := pair; cases prime <;> simp only [Proof.Ffdh.candidateStatus] <;> decide
  have value : s.gpr .r0 = BitVec.ofNat 32 (Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used)) := by
    rw [← h.2.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (compareResult_ok s small which value) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.1.after_read (by decide) mem rest, h.2.after_read mem rest (by decide)⟩,
    by change some t.z = _; rw [flag]⟩

private theorem compare_ct (test : Nat) (which : test = 1 ∨ test = 2) :
    RelCT isa (Two PostCT) (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) (Two (ComparisonCT test)) := by
  rcases which with rfl | rfl
  all_goals exact two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (by taint_decide) (compare_ready _ (by decide))

theorem classify_ct : RelCT isa (Two PostCT) VG.Impl.Ffdh.Arm.ParameterSearch.classify (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.classify
  refine RelCT.seq (compare_ct 1 (Or.inl rfl)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact accepted_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
      ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1.1⟩, ⟨q.used, q.remaining, ht.1.1.1⟩, sp⟩) (fun _ _ h => h)
  · refine RelCT.seq ((compare_ct 2 (Or.inr rfl)).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)) ?_
    refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
    · exact rejected_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
        ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1.1⟩, ⟨q.used, q.remaining, ht.1.1.1⟩, sp⟩) (fun _ _ h => h)
    · exact short_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1.1, ht.1.1.1, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterSearch
