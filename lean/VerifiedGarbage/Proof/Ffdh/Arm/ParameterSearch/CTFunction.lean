module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Function
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Body
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Loop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Widen
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start

/-! Native entry, complete bounded search, return stores and saved frame satisfy relational timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

theorem body_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two SearchStart)
    (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.body
  refine RelCT.seq (two_post entry_ct entry_ready) ?_
  exact (loop_ct backend).mono
    (fun _ _ ⟨p, hs, ht, sp⟩ => ⟨initialPoint p, hs, ht, sp⟩) (fun _ _ h => h)

private theorem body_ready (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    (p : SearchParams) (s : State) (h : SearchStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s (DoneCT p) :=
  WP.mono (body_ok backend h) fun _ ⟨done, _⟩ => ⟨_, done⟩

theorem function_body_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two SearchStart)
    (.seq (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (.block VG.Impl.Ffdh.Arm.ParameterSearch.finish)) (fun _ _ => True) :=
  RelCT.seq (two_post (body_ct backend) (body_ready backend)) finish_ct

private theorem pushed_start {p : SearchParams} {s : State} (h : FunctionInput p s) : SearchStart p (searchPushed s) := by
  have result := h.start.withRegions (body_reads s) (fun _ member => List.mem_cons_of_mem _ member)
  simpa only [bodyState, State.withRegions_withRegions, State.withRegions_self] using result

private theorem push_search_eq {s t : State}
    (h : isa.push (.push [.r4, .r9, .r10, .r11, .r12, .lr]) s = some t) : t = searchPushed s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem function_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two FunctionInput)
    (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.code
  refine RelCT.frame (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (function_body_ct backend).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨p, hs, ht, sp⟩, pushS, pushT⟩
  have first := push_search_eq pushS
  have second := push_search_eq pushT
  subst first second
  refine ⟨p, pushed_start hs, pushed_start ht, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.ParameterSearch
