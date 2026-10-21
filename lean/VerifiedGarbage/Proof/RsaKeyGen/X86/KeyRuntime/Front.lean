module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.IOFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Shared arithmetic composes with the established input and output contracts -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input BodyOutcome stage_scratch_frame
  deriveArrays prepareArrays keyPartArrays)

theorem front_ok {E : Environment} {s : State} (h : Input E s) (H : Ws s E.base E.size E.n 32) :
    WP isa front s fun t => VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  unfold front
  refine WP.seq (WP.mono (loadInputs_front h H) fun u ⟨L, Hu, Fu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (deriveLoaded_ok Hu widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 L.pBound L.qBound L.zero L.one L.loaded)
    fun v ⟨Hv, Ov, result, Kv⟩ => ?_)
  rw [L.eValue, L.pValue, L.qValue] at result
  have Iv := L.input.afterStage Hv.old Kv Ov
  have Fv := stage_scratch_frame L.input.ws (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) Ov
  refine WP.mono (writeCore_front Iv result) fun t ⟨ht, written, Ft, Kt⟩ => ?_
  refine ⟨ht, written, ?_, Ku.trans (Kv.trans Kt)⟩
  have prefixFrame : Frame E.outputs.writes s.mem v.mem := (Fu.trans Fv).mono (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact List.mem_cons_self ..)
  exact prefixFrame.trans Ft

end VG.Proof.RsaKeyGen.X86.KeyRuntime
