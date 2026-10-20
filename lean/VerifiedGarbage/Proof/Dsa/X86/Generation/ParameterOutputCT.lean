module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeParameterSearch
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputCT
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputCT

/-! # Final copying versus zeroing is selected by the public parameter-search result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def ParameterFinalAt (P : SearchContextPlan) (s : State) : Prop :=
  ∃ initial, ParameterFinished P (parameterRemaining P 0 0) initial s

theorem parameterFinal_frame {P : SearchContextPlan} {s : State} (H : ParameterFinalAt P s) :
    FrameAt [5, 6, 7] ⟨P.geometry.frameBase, P.saved⟩ s := by
  obtain ⟨_, W, R, _⟩ := H
  exact ⟨R.arena.frame, fun i hi => (R.representation i (by simp_all; omega)).trans
    (R.fixed i (by simp_all; omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> decide))⟩

theorem parameterOutput_ct : RelCT isa (Two ParameterFinalAt) finishOutput (fun _ _ => True) := by
  unfold finishOutput
  refine RelCT.seq (two_piece (Ψ := fun P s => FrameAt [5, 6, 7] ⟨P.geometry.frameBase, P.saved⟩ s ∧
    s.zf = some (parameterRemaining P 0 0).isSome) [.esp] ?_ (by taint_decide) ?_) ?_
  · intro P s t hs ht r hr
    exact frameAt_pins _ _ s t (parameterFinal_frame hs) (parameterFinal_frame ht) r hr
  · intro P s H
    have frame := parameterFinal_frame H
    obtain ⟨_, W, R, result, _⟩ := H
    refine WP.mono (frameSuccess_ok R.arena.frame R.representation) fun t ⟨zf, mem, K⟩ => ?_
    refine ⟨frame.keep mem K (by decide), ?_⟩
    rw [zf]
    rcases result with ⟨status, expected⟩ | ⟨params, status, expected, _⟩
    · rcases status with h | h <;> rw [h, expected] <;> rfl
    · rw [status, expected]; rfl
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · exact two_map (fun P => ⟨P.geometry.frameBase, P.saved⟩) (fun _ _ h => h.1.1) outputCopy_ct
    · exact two_map (fun P => ⟨P.geometry.frameBase, P.saved⟩)
        (fun _ _ h => ⟨h.1.1.1, fun i hi => h.1.1.2 i (by simp_all)⟩) outputZero_ct
end VG.Proof.Dsa.X86.Generation
