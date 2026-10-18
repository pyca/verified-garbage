module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptMaskArgs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.MaskLoop
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-! # Masked output bytes and the exact output memory frame -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes

theorem mask_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (src : s.gpr .esi = g.output) (count : s.gpr .ecx = BitVec.ofNat 32 g.length) :
    WP isa VG.Impl.RsaPkcs1Enc.X86.maskLoop s fun t => Context g bs t ∧
      Frame [g.outputRegion] s.mem t.mem ∧ Keeps [.eax, .esi, .ecx] s t ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
        (Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length).map fun b => b &&& (s.gpr .edx).setWidth 8 := by
  refine WP.mono (maskLoop_ok (by have := h.valid.minLength; omega) h.valid.maxLength
    (by rw [src]; exact h.valid.outputFit) ?_ count) ?_
  · intro i hi
    rw [src, byteAddr_add (by have := h.valid.outputFit; omega)]
    exact CallLay.inRegions_sub (off := i) h.outputWrite (by omega) (by have := h.valid.maxLength; omega)
  · rintro t ⟨K, M⟩
    rw [masked, src] at M
    have len : ((Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length).map
        (fun b => b &&& (s.gpr .edx).setWidth 8)).length = g.length := by
      simp only [List.length_map, VG.Proof.Bignum.bytesAt_length]
    have F : Frame [g.outputRegion] s.mem t.mem := by
      rw [M]
      apply writeBytes_frame
      rw [len]
      exact Region.contains_self _ _
    refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
    · rw [M]
      have bytes := VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes s.mem (byteAddr g.output)
        ((Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length).map (fun b => b &&& (s.gpr .edx).setWidth 8))
        (by rw [len]; have := h.valid.maxLength; omega)
      rw [len] at bytes
      exact bytes

end VG.Proof.RsaPkcs1Enc.X86.Enc
