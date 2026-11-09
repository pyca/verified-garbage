module

public import VerifiedGarbage.Proof.ChaCha20.X86.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86

/-! # Streaming ChaCha20 (RFC 8439) on x86 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.init
    verified := Proof.ChaCha20.X86.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.setNonce
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified } ]

end VG.Artifacts.ChaCha20.X86

-- Streaming ChaCha20 (RFC 8439) on x86: `vg_chacha20_apply`
namespace VG.Artifacts.ChaCha20.X86.ChaCha20Xor

def artifacts (v : Proof.ChaCha20.X86.XorImpl) : List Artifact := [
  Spec.ChaCha20.applyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.ChaCha20.X86.Stream.apply v.callee
    stack := 32
    verified := Proof.ChaCha20.X86.Stream.apply_verified v
    spSafe := Proof.ChaCha20.X86.Stream.apply_spSafe v
    features := v.features }]

end VG.Artifacts.ChaCha20.X86.ChaCha20Xor

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86.variants.flatMap fun v => ChaCha20Xor.artifacts v)

end VG.Artifacts.ChaCha20.X86
