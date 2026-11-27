module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Impl.ChaCha20.AArch64.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on AArch64 -/

namespace VG.Artifacts.ChaCha20.AArch64

def direct : List (Artifact AArch64.target) := [
  Spec.ChaCha20.initApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Fn.init
    verified := Proof.ChaCha20.AArch64.Stream.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Fn.setNonce
    verified := Proof.ChaCha20.AArch64.Stream.setNonce_scrubbed }]

public def artifacts : List (Artifact AArch64.target) :=
  direct ++ VG.Proof.Variants.ChaCha20Xor.AArch64.variants.flatMap fun v => [
    Spec.ChaCha20.applyApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20.AArch64.Fn.apply v.callee
      verified := Proof.ChaCha20.AArch64.Fn.apply v }]

spec_apis artifacts

end VG.Artifacts.ChaCha20.AArch64
