module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86 -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86.ChaCha20Poly1305

def artifacts (v : Proof.ChaCha20.X86.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee)
    stack := 772
    verified := Proof.ChaCha20Poly1305.X86.seal_framed v
    spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
      (Proof.ChaCha20Poly1305.X86.seal_spSafe v)
    features := v.features },
  Spec.ChaCha20Poly1305.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» v.callee)
    stack := 772
    verified := Proof.ChaCha20Poly1305.X86.open_framed v
    spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
      (Proof.ChaCha20Poly1305.X86.open_spSafe v)
    features := v.features },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.ChaCha20Poly1305.X86.SealGather.sealGather (Proof.ChaCha20Poly1305.X86.Gather.sealFn v).name
      (Proof.ChaCha20Poly1305.X86.Gather.sealFn v).code
    stack := 824
    verified := Proof.ChaCha20Poly1305.X86.Gather.sealGather_verified (Proof.ChaCha20Poly1305.X86.Gather.sealFn v)
    spSafe := Proof.ChaCha20Poly1305.X86.Gather.sealGather_spSafe v
    features := v.features }]

end VG.Generic.ChaCha20Xor.X86.ChaCha20Poly1305
