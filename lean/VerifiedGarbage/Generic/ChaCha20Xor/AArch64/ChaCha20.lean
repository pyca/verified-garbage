module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ChaCha20 (RFC 8439) on AArch64: `vg_chacha20_apply` -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  Spec.ChaCha20.applyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    code := Impl.ChaCha20.AArch64.Stream.apply v.callee
    verified := Proof.ChaCha20.AArch64.Stream.apply_verified v
    features := v.features }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20
