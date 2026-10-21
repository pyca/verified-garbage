module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside

/-! # The established input adapters preserve the runtime argument records -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Ws.afterFrame {s t : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    (h : Ws s B Z n N) (K : Keeps rs s t) (F : Frame [⟨B, Z⟩] s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N := by
  have frame : Frame [⟨off B 0, Z⟩] s.mem t.mem := by
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using F
  exact h.keep K (VG.Proof.RsaKeyGen.frame_outside frame
    (by have := h.old.workspace.nowrap; omega)) edi esp

end VG.Proof.RsaKeyGen.X86.KeyRuntime
