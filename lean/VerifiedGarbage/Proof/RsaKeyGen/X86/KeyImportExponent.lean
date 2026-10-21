module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadFrames
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exponent import through the retained public key arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem Input.importExponent {E : Environment} {s : State} (h : Input E s) :
    WP isa (loadExponent E.n) s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧
      val32 t.mem E.base kEv 2 = Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem E.exponentRegion.base E.exponentRegion.len) ∧
      num t.mem E.base E.n aE = val32 t.mem E.base kEv 2 ∧
      (∀ j, j < 32 → j ≠ aE → num t.mem E.base E.n j = num s.mem E.base E.n j) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  have head := h.ws.hdr_le
  refine WP.mono (loadExponent_ok h.ws (by omega) h.valid.exponentLength.1 h.valid.exponentLength.2
    (h.arguments 14 (by decide)) (h.arguments 15 (by decide)) h.valid.exponentFit h.exponentRead
    (h.valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv hdr at *; omega))))
    fun t ⟨ht, O, value, loaded, K⟩ => ?_
  refine ⟨h.afterExponent ht K O, loadExponent_scratch_frame h.ws O, value, loaded, ?_, K.mono (by decide)⟩
  intro j hj different
  exact loadExponent_preserves_num different (h.ws.fit64 hj) O

end VG.Proof.RsaKeyGen.X86.Key
