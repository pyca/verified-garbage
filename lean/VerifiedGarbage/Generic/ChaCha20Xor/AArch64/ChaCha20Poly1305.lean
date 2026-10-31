module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64 -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
      (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)
    stack := 1280
    verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v },
  Spec.ChaCha20Poly1305.openApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
      (Impl.ChaCha20Poly1305.AArch64.openCode v.callee v.stitched)
    stack := 1280
    verified := Proof.ChaCha20Poly1305.AArch64.open_framed v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather (Proof.ChaCha20Poly1305.AArch64.sealFn v).name (Proof.ChaCha20Poly1305.AArch64.sealFn v).code
    stack := 1296
    verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified (Proof.ChaCha20Poly1305.AArch64.sealFn v) }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305
