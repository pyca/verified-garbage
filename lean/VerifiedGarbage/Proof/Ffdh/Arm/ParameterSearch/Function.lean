module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Push
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Body
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Widen
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Execute the full native function while keeping its saved frame read-only during search. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

structure FunctionInput (p : SearchParams) (s : State) : Prop where
  stackFits : 232 ≤ s.sp.toNat
  start : SearchStart p (bodyState s)
  savedWrites : ∀ r ∈ s.wr, (⟨State.addr (bodyState s).sp, 24⟩ : Region).Disjoint r

theorem function_body (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : FunctionInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (searchPushed s) (FinishInput p s (p.tail 0 p.attempts)) := by
  obtain ⟨tr, t, run, done, rest, frame⟩ := body_run backend h.start
  have fit : 24 ≤ s.sp.toNat := by have := h.stackFits; omega
  have saved : Spill.Saved t.mem (State.addr t.sp) s.gpr savedSlots := by
    rw [rest.sp]
    apply (push_saved s fit).frame (lo := 0) (hi := 24) (by decide) frame
    intro r member
    have separate : (⟨State.addr (bodyState s).sp, 24⟩ : Region).Disjoint r := by
      rcases List.mem_append.mp member with original | below
      · exact h.savedWrites r original
      · obtain rfl := List.mem_singleton.mp below
        have below : 208 ≤ (bodyState s).sp.toNat := h.start.storage.below
        rw [FrameStack.belowA, FrameStack.addr_sub' below]
        exact VG.Offset.base_disjoint_below _ (by decide : 208 + 24 ≤ 2 ^ 64)
    simpa only [BitVec.add_zero, Nat.sub_zero] using separate
  have widened := Exec.widen run (body_reads s) (body_writes s)
  have runWide : Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (searchPushed s) tr (t.withRegions (searchPushed s).rd (searchPushed s).wr) := by
    simpa only [bodyState, State.withRegions_withRegions, State.withRegions_self] using widened
  refine ⟨tr, _, runWide, ?_⟩
  refine ⟨done.withRegions ?_ ?_, saved, rest.sp, fit, ?_⟩
  · rw [rest.rd, rest.wr]
    exact body_reads s
  · intro r member
    rw [rest.wr] at member
    exact List.mem_cons_of_mem _ member
  · intro r member
    exact rest.gpr r (by cases r <;> simp_all [bodyClobbers])

theorem function_ok (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : FunctionInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) s
      fun t => abiPreserved s t ∧ ResultPost p (p.tail 0 p.attempts) t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.code
  refine WP.frame (by decide) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega) (by decide) ?_
  rw [WP.seq_iff]
  exact WP.mono (function_body backend h) fun _ input => finish_ok input

end VG.Proof.Ffdh.Arm.ParameterSearch
