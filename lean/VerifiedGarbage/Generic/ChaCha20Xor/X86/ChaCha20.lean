module

public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Streaming ChaCha20 (RFC 8439) on x86: `vg_chacha20_apply` -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86.ChaCha20

def artifacts (v : Proof.ChaCha20.X86.XorImpl) : List Artifact := [
  Spec.ChaCha20.applyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.ChaCha20.X86.Stream.apply v.callee
    stack := 32
    verified := Proof.ChaCha20.X86.Stream.apply_verified v
    spSafe := Proof.ChaCha20.X86.Stream.apply_spSafe v
    features := v.features }]

end VG.Generic.ChaCha20Xor.X86.ChaCha20
