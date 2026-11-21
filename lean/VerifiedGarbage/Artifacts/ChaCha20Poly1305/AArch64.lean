module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.SealGather
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.AArch64

def artifacts : List Artifact :=
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

end VG.Artifacts.ChaCha20Poly1305.AArch64
