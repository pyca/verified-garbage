module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Stream
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ChaCha20 (RFC 8439) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.AArch64

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Fn.init
    verified := .scrubbed Proof.ChaCha20.AArch64.Stream.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Fn.setNonce
    verified := .scrubbed Proof.ChaCha20.AArch64.Stream.setNonce_scrubbed }]

def artifacts : List Artifact :=
  direct ++ VG.Proof.Variants.ChaCha20Xor.AArch64.variants.flatMap fun v => [
    Spec.ChaCha20.applyApi.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.ChaCha20.AArch64.Fn.apply v.callee
      verified := .scrubbed (Proof.ChaCha20.AArch64.Fn.apply v) }]

end VG.Artifacts.ChaCha20.AArch64
