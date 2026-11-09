module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64

/-! # Streaming ChaCha20 (RFC 8439) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.AArch64

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Stream.init
    verified := Proof.ChaCha20.AArch64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Stream.setNonce
    verified := Proof.ChaCha20.AArch64.Stream.setNonce_verified }]

end VG.Artifacts.ChaCha20.AArch64

-- ChaCha20 (RFC 8439) on AArch64: `vg_chacha20_apply`
namespace VG.Artifacts.ChaCha20.AArch64.ChaCha20Xor

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  Spec.ChaCha20.applyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    code := Impl.ChaCha20.AArch64.Stream.apply v.callee
    verified := Proof.ChaCha20.AArch64.Stream.apply_verified v
    features := v.features }]

end VG.Artifacts.ChaCha20.AArch64.ChaCha20Xor

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.AArch64.variants.flatMap fun v => ChaCha20Xor.artifacts v)

end VG.Artifacts.ChaCha20.AArch64
