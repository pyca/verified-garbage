module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.IOFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputStage
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Shared arithmetic composes with the established input and output contracts -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input BodyOutcome stage_scratch_frame
  deriveArrays prepareArrays keyPartArrays)

theorem front_ok {E : Environment} {p : BitVec 32} {s : State} (h : Input E s) (H : Ws s E.base E.size E.n 32)
    (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s)
    (apart : ∀ i < 7, (VG.Proof.RsaKeyGen.X86.KeyArgs.argsRegion p).Disjoint (E.outputRegion i)) :
    WP isa front s fun t => VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame (E.outputs.writes ++ [below p 52]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  unfold front
  refine WP.seq (WP.mono (loadInputs_front h H C) fun u ⟨L, Hu, Fu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (deriveLoaded_ok Hu widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 L.pBound L.qBound L.zero L.one L.loaded)
    fun v ⟨Hv, Ov, result, Kv⟩ => ?_)
  rw [L.eValue, L.pValue, L.qValue] at result
  have Iv := input_afterStage L.input Hu Hv.old Kv Ov
  have Cu := C.keep Ku Fu
  have spU : u.gpr .esp = p := Cu.sp
  have Fv : Frame ([⟨E.base, E.size⟩] ++ [below p 52]) u.mem v.mem := by
    rw [← spU]
    exact Ov.toFrame fun _ _ O =>
      stage_scratch_frame L.input.ws (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O
  have Cv := Cu.keepBelow Kv Fv
  refine WP.mono (writeCore_front Iv Cv apart result) fun t ⟨ht, written, Ft, Kt⟩ => ?_
  refine ⟨ht, written, ?_, Ku.trans (Kv.trans Kt)⟩
  have wsIn : E.workspaceRegion ∈ E.outputs.writes ++ [below p 52] :=
    List.mem_append_left _ List.mem_cons_self
  have prefixFrame : Frame (E.outputs.writes ++ [below p 52]) s.mem v.mem :=
    (Fu.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact wsIn)).trans (Fv.mono (by
      intro r hr
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact wsIn
      · exact List.mem_append_right _ (List.mem_singleton_self _)))
  exact prefixFrame.trans (Ft.mono fun r hr => List.mem_append_left _ hr)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
