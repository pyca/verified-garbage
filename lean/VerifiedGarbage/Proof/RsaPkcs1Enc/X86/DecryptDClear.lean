module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptDArgs
public import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
public import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Initialize the complete fixed-width private-exponent buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem clearD_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (src : s.gpr .esi = g.workspace + BitVec.ofNat 32 sD)
    (count : s.gpr .ecx = BitVec.ofNat 32 g.length) (zero : s.gpr .eax = 0) :
    WP isa (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne) s fun t => Context g bs t ∧
      Frame [g.scratch sD g.length] s.mem t.mem ∧ Keeps [.esi, .ecx] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base g.length = List.replicate g.length 0 := by
  have fit : sD + g.length ≤ 8448 := by have := h.valid.maxLength; unfold sD; omega
  have addr : (g.workspace + BitVec.ofNat 32 sD).setWidth 64 = (g.scratch sD g.length).base :=
    h.valid.scratchAddress (by decide : sD < 8448)
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok
    (by have := h.valid.minLength; omega) (by have := h.valid.maxLength; omega)
    (h.valid.scratchFit fit (by decide)) src count zero ?_) ?_
  · intro i hi
    rw [addr]
    change InRegions s.wr (byteAddr g.workspace + BitVec.ofNat 64 sD + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact h.scratchWrite (d := sD + i) (by omega)
  · rintro t ⟨Z, _, O, K⟩
    have F : Frame [g.scratch sD g.length] s.mem t.mem := by
      have raw := outside_frame O (by have := h.valid.maxLength; omega)
      simpa only [VG.Proof.Mont.off, BitVec.add_zero, addr, Geometry.scratch] using raw
    refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.workspaceRegion, by simp [bodyWrites], h.valid.scratchSub fit⟩
    · rw [addr] at Z
      exact Z

end VG.Proof.RsaPkcs1Enc.X86.Dec
