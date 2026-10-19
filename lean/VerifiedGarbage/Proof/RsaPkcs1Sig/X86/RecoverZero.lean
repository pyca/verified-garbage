module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
public import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
public import VerifiedGarbage.Proof.Bignum.FrameOutside

/-! # Invalid encodings clear every output byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover

theorem zeroArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)]) s
      fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.esi, .ecx, .eax] s t ∧
        t.gpr .esi = g.output ∧ t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .eax = 0 := by
  unfold incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 0 < 13)) fun a A => ?_
  have ha : Context g bs a := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine wp_ldm rfl (ha.readArg (by decide : 1 < 13)) fun b B => ?_
  refine wp_movS rfl fun c C _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, C.gpr⟩
  · rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, h.argumentValue (by decide : 0 < 13)]; rfl
  · rw [C.other .ecx (by decide), B.gpr, ha.argumentValue (by decide : 1 < 13)]; rfl

theorem zeroOut_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa zeroOut s fun t => Context g bs t ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.outputLength = List.replicate g.outputLength 0 ∧
      t.gpr .eax = 0 ∧ Frame [g.outputRegion] s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  unfold zeroOut incoming stackAt
  refine WP.seq (wp_ldm rfl (h.readArg (by decide : 0 < 13)) fun a A => ?_)
  have ha : Context g bs a := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine wp_ldm rfl (ha.readArg (by decide : 1 < 13)) fun b B => ?_
  refine wp_movS rfl fun c C _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have k32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok
    (by have := h.valid.outputPositive; omega) k32 h.valid.outputFit
    (by rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, h.argumentValue (by decide : 0 < 13)]; rfl)
    (by rw [C.other .ecx (by decide), B.gpr, ha.argumentValue (by decide : 1 < 13)]; rfl) C.gpr ?_) ?_
  · intro i hi
    rw [K.2.2]
    exact CallLay.inRegions_sub (off := i) h.outputWrite (by omega) (by omega)
  · rintro t ⟨V, Z, O, T⟩
    have F : Frame [g.outputRegion] s.mem t.mem := by
      rw [M] at O
      simpa only [VG.Proof.Mont.off, BitVec.add_zero, Geometry.outputRegion, byteAddr] using outside_frame O (by omega)
    have keep := K.trans (T.mono (by decide))
    refine ⟨h.after (F.sub ?_) keep (keep.1 .esp (by decide)), V, Z, F, keep⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
