module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTCall
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTClassify
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLeaf
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTRequest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Call
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState

/-! The native search step selects its public entropy-length path and calls the proved candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_piece two_post two_ite)

def LengthCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧
  isa.eval .eq s = some (decide (q.inputs.c.bytes.length - q.used < q.inputs.c.length))

private theorem length_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s (LengthCT q) := by
  refine WP.mono h.length_guard ?_
  rintro t ⟨⟨live, flag, _⟩, _⟩
  exact ⟨live, by change some t.z = _; rw [flag]⟩

private theorem zero_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut s (LiveCT q) :=
  WP.mono h.zero_output fun _ ⟨live, _⟩ => live

private theorem run_ready (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    (q : SearchPoint) (s : State) (h : ReadyCT q s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun (.call backend.candidateName backend.candidate)) s (PostCT q) :=
  WP.mono (candidateRun_ok backend h.1 h.2) fun _ ⟨data, _⟩ => data

theorem step_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two LiveCT)
    (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) length_ready) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · have zeroTrace : RelCT isa (Two LiveCT) VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut (fun _ _ => True) :=
      zero_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
        ⟨q.inputs, ⟨q.used, q.remaining, hs⟩, ⟨q.used, q.remaining, ht⟩, sp⟩) (fun _ _ h => h)
    exact (RelCT.seq (two_post zeroTrace zero_ready) request_ct).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)
  · have ready (q : SearchPoint) (s : State) (h : LengthCT q s ∧ isa.eval .eq s = some false) : ReadyCT q s := by
      have enough := of_decide_eq_false (Option.some.inj (h.1.2.symm.trans h.2))
      exact ⟨h.1.1, by have := h.1.1.usedBound; omega⟩
    exact (RelCT.seq (two_post (candidate_run_ct backend) (run_ready backend)) classify_ct).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, ready q _ hs, ready q _ ht, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterSearch
