module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInitialize
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Initialized native workspace retains the public key environment -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem Input.initialize_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (clearArrays E.n) s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧
      num t.mem E.base E.n aOne = 1 ∧
      (∀ j, j < 32 → j ≠ aOne → num t.mem E.base E.n j = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine WP.mono (clearArrays_ok h.ws) fun t ⟨ht, O, one, zero, K⟩ => ?_
  refine ⟨h.afterOuts ht K ?_ O, ?_, one, zero, K.mono (by decide)⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (by decide : 72 ≤ hdr)
  · exact outs_scratch_frame (by have := h.ws.workspace.nowrap; omega) O
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.ws.fits)

end VG.Proof.RsaKeyGen.X86.Key
