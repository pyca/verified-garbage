module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext

import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # The call return address does not alter the private candidate or packed public key -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem PrivContext.callFrame {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.X86.below_top (by decide : 4 ≤ 24) h.valid.stackLow (by decide : 4 ≤ 4))

theorem PrivContext.callTemporary {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length := by
  apply rsa_bytes_frame h.callFrame (by have := h.valid.maxLength; omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  apply (h.valid.calleeInner.sub_right ?_).symm
  rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
  exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)

theorem PrivContext.callPrecomputation {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) :
    Spec.Rsa.wordsAt s.callEntry.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
      Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) := by
  apply wordsAt_frame h.callFrame (by have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  apply (h.valid.calleeInner.sub_right ?_).symm
  rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
  exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega)

end VG.Proof.Rsa.X86.PrivChecked
