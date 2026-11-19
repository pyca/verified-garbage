module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.ChaCha20Xor.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.ChaCha20.AArch64.XorImpl // v ∈ VG.Proof.Variants.ChaCha20Xor.AArch64.variants }) => [
    Spec.ChaCha20Poly1305.sealApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.callee.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.sealCode v.1.callee v.1.stitched)
      verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v.1 }
      (AArch64.ScrubAll.clearUnion Proof.ChaCha20Poly1305.AArch64.Scrub.sealOwn v.1.clear)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.sealOk 1280)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.sealSide v.1 v.2)),
    Spec.ChaCha20Poly1305.openZeroApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.callee.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 1312 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.openInPlace v.1.callee v.1.stitched)
      verified := Proof.ChaCha20Poly1305.AArch64.open_framed v.1 }
      (AArch64.ScrubAll.clearUnion Proof.ChaCha20Poly1305.AArch64.Scrub.openOwn v.1.clear)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.openOk 1312)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.openSide v.1 v.2)),
    Spec.ChaCha20Poly1305.openToApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.callee.suffix
      code := Impl.StackScratch.AArch64.withStackArgScratchWiped 1328 1 96
        (Impl.ChaCha20Poly1305.AArch64.openTo v.1.callee v.1.stitched)
      verified := Proof.ChaCha20Poly1305.AArch64.openTo_framed v.1 }
      (AArch64.ScrubAll.clearUnion Proof.ChaCha20Poly1305.AArch64.Scrub.openOwn v.1.clear)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.openToOk 1328)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.openToSide v.1 v.2)),
    Spec.ChaCha20Poly1305.sealGatherApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.callee.suffix
      code := Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather
        (Proof.ChaCha20Poly1305.AArch64.Scrub.sealFnCore v.1).name
        (Proof.ChaCha20Poly1305.AArch64.Scrub.sealFnCore v.1).code
      verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified
        (Proof.ChaCha20Poly1305.AArch64.Scrub.sealFnCore v.1) }
      (AArch64.ScrubAll.clearUnion Proof.ChaCha20Poly1305.AArch64.Scrub.sealOwn v.1.clear)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.gatherOk 1296)
      (Proof.ChaCha20Poly1305.AArch64.Scrub.gatherSide v.1 v.2))]

end VG.Artifacts.ChaCha20Poly1305.AArch64
