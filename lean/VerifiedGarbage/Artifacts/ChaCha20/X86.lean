module

public import VerifiedGarbage.Proof.ChaCha20.X86.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Streaming ChaCha20 (RFC 8439) on x86 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.init
    verified := Proof.ChaCha20.X86.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.setNonce
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified } ]

end VG.Artifacts.ChaCha20.X86
