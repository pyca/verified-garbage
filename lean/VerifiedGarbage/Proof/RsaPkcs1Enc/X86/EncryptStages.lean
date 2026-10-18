module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncodingTiming
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptCallPublic
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptAfter

/-! # Public intermediate states used to compose encryption timing proofs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt

structure CallReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  arguments : Arguments g (publicArgument g) 10 s

structure MaskReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  src : s.gpr .esi = g.output
  count : s.gpr .ecx = BitVec.ofNat 32 g.length

theorem start_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block start) s (EncodeReady g bs) := by
  refine WP.mono (start_ok h) ?_
  rintro t ⟨ht, _, _, dst, src, count⟩
  exact ⟨ht, dst, src, count⟩

theorem encoding_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EncodeReady g bs s) : WP isa encoding s (Context g bs) := by
  refine WP.mono (encoding_ok h.context h.dst h.src h.count) ?_
  rintro t ⟨ht, _⟩
  exact ht

theorem callArgs_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block callArgs) s (CallReady g bs) := by
  refine WP.mono (callArgs_ok h) ?_
  rintro t ⟨ht, args, _⟩
  exact ⟨ht, args⟩

theorem publicCall_done (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : CallReady g bs s) : WP isa (.call v.name v.code) s (Context g bs) := by
  refine WP.mono (public_call v h.context h.arguments) ?_
  rintro t ⟨ht, _⟩
  exact ht

theorem maskArgs_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block maskArgs) s (MaskReady g bs) := by
  refine WP.mono (maskArgs_ok h) ?_
  rintro t ⟨ht, _, _, _, _, src, count⟩
  exact ⟨ht, src, count⟩

theorem mask_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : MaskReady g bs s) : WP isa VG.Impl.RsaPkcs1Enc.X86.maskLoop s (Context g bs) := by
  refine WP.mono (mask_ok h.context h.src h.count) ?_
  rintro t ⟨ht, _⟩
  exact ht

end VG.Proof.RsaPkcs1Enc.X86.Enc
