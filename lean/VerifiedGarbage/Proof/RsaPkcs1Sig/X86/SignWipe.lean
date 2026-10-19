module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipeArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
public import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
public import VerifiedGarbage.Proof.Bignum.FrameOutside

/-! # Erase the complete temporary encoding while preserving the result status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Sign

theorem wipe_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : WP isa wipe s fun t => Context g bs t ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 ∧
      t.gpr .eax = s.gpr .eax ∧ Frame [g.innerRegion] s.mem t.mem ∧ Keeps [.ebx, .eax, .esi, .ecx] s t := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_ok h) ?_)
  rintro u ⟨hu, M, K, status, zero, src, cnt⟩
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.failureLoop_ok
    (by have := h.valid.minLength; omega) (by have := h.valid.maxLength; omega)
    h.valid.temporaryFit src cnt zero ?_) ?_)
  · intro i hi
    exact CallLay.inRegions_sub (off := i) hu.temporaryWrite (by omega) (by have := h.valid.maxLength; omega)
  · rintro v ⟨V, Z, O, T⟩
    have F : Frame [g.innerRegion] s.mem v.mem := by
      rw [M] at O
      have raw := outside_frame O (by have := h.valid.maxLength; omega)
      apply raw.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simpa only [VG.Proof.Mont.off, BitVec.add_zero, Geometry.outputRegion, byteAddr] using h.temporarySub
    have keep := K.trans (T.mono (by decide))
    refine wp_movS rfl fun t U _ => WP.block_nil ?_
    have kt := keep.trans (U.keeps.mono (by decide))
    have ft : Frame [g.innerRegion] s.mem t.mem := by rw [U.mem]; exact F
    refine ⟨h.after (ft.sub ?_) kt (kt.1 .esp (by decide)), ?_, ?_, ft, kt⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
    · rw [U.mem]; exact V
    · rw [U.gpr, T.1 .ebx (by decide), status]

end VG.Proof.RsaPkcs1Sig.X86.Sgn
