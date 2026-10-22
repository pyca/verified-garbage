module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProtectedContext
public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry

/-! # Save and restore the protected array-four prefix -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem saveArray_ok {s : State} {base : Addr} {bytes w : Nat}
    (h : ProtectedContext s base bytes) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa saveArray s
      (TransferResult s (ptr32 base (arrAt w 4)) (ptr32 (byteAddr (s.gpr .esp)) savedArray) (8 * w)) := by
  have bound : arrAt w 4 + 8 * w ≤ bytes := by
    have := array_fits_bytes hf (show 4 < 28 by decide)
    omega
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  unfold saveArray
  apply h.to_stack (by omega) (by omega) bound (saved_array_fits_frame hu)
  simp only [List.append_assoc]
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc h.ws h52, hwidth]) hu h.ws.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  refine stackPointer_ok fun s₂ K₂ m₂ p₂ => ?_
  have KK : Keeps transferClobbers s s₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := h.ws.of_keeps KK (by decide)
  refine width_ok (by rw [readSrc_sc hs₂ h52, m₂, m₁, hwidth]) fun t K₃ m₃ p₃ => WP.block_nil ?_
  refine ⟨KK.trans (K₃.mono (by decide)), by rw [m₃, m₂, m₁], ?_, ?_, p₃⟩
  · rw [K₃.1 .esi (by decide), K₂.1 .esi (by decide)]
    exact ptrAt_eq p₁
  · rw [K₃.1 .ebx (by decide), p₂, K₁.1 .esp (by decide)]
    exact ptr32_stack _ _

theorem restoreArray_ok {s : State} {base : Addr} {bytes w : Nat}
    (h : ProtectedContext s base bytes) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa restoreArray s
      (TransferResult s (ptr32 (byteAddr (s.gpr .esp)) savedArray) (ptr32 base (arrAt w 4)) (8 * w)) := by
  have bound : arrAt w 4 + 8 * w ≤ bytes := by
    have := array_fits_bytes hf (show 4 < 28 by decide)
    omega
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  unfold restoreArray
  apply h.from_stack (by omega) (by omega) bound (saved_array_fits_frame hu)
  simp only [List.append_assoc]
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc h.ws h52, hwidth]) hu h.ws.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  refine stackPointer_ok fun s₂ K₂ m₂ p₂ => ?_
  have KK : Keeps transferClobbers s s₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := h.ws.of_keeps KK (by decide)
  refine width_ok (by rw [readSrc_sc hs₂ h52, m₂, m₁, hwidth]) fun t K₃ m₃ p₃ => WP.block_nil ?_
  refine ⟨KK.trans (K₃.mono (by decide)), by rw [m₃, m₂, m₁], ?_, ?_, p₃⟩
  · rw [K₃.1 .esi (by decide), p₂, K₁.1 .esp (by decide)]
    exact ptr32_stack _ _
  · rw [K₃.1 .ebx (by decide), K₂.1 .ebx (by decide)]
    exact ptrAt_eq p₁

end VG.Proof.MillerRabin.X86
