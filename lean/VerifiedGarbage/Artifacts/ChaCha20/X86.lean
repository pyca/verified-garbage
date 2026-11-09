module

public import VerifiedGarbage.Proof.ChaCha20.X86.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86

/-! # ChaCha20 (RFC 8439) on x86 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.init
    verified := Proof.ChaCha20.X86.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.setNonce
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified } ]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86.variants.flatMap fun (v : Proof.ChaCha20.X86.XorImpl) => [
    Spec.ChaCha20.applyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20.X86.Stream.apply v.callee
      stack := 32
      verified := Proof.ChaCha20.X86.Stream.apply_verified v
      spSafe := Proof.ChaCha20.X86.Stream.apply_spSafe v }])

end VG.Artifacts.ChaCha20.X86
