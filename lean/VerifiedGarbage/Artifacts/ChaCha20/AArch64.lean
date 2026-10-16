module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The ChaCha20 block function (RFC 8439) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact := [
  Spec.ChaCha20.blockApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.block
    verified := Proof.ChaCha20.AArch64.block_verified },
  Spec.ChaCha20.initApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Stream.init
    verified := Proof.ChaCha20.AArch64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact AArch64.target {
    code := Impl.ChaCha20.AArch64.Stream.setNonce
    verified := Proof.ChaCha20.AArch64.Stream.setNonce_verified }]

end VG.Artifacts.ChaCha20.AArch64
