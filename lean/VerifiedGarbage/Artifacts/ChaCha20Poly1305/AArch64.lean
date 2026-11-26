module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.SealGather
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64 -/

namespace VG.Artifacts.ChaCha20Poly1305.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.ChaCha20Xor.AArch64.variants.flatMap fun v => [
    Spec.ChaCha20Poly1305.sealApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched
      verified := Proof.ChaCha20Poly1305.AArch64.Fn.sealWhole v },
    Spec.ChaCha20Poly1305.openZeroApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20Poly1305.AArch64.Fn.openZero v.callee v.stitched
      verified := Proof.ChaCha20Poly1305.AArch64.Fn.openZero v },
    Spec.ChaCha20Poly1305.openToApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20Poly1305.AArch64.Fn.openTo v.callee v.stitched
      verified := Proof.ChaCha20Poly1305.AArch64.Fn.openTo v },
    Spec.ChaCha20Poly1305.sealGatherApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20Poly1305.AArch64.Fn.sealGather v.callee v.stitched
      verified := Proof.ChaCha20Poly1305.AArch64.Fn.sealGather v }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.AArch64
