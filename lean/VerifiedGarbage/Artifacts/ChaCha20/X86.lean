module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.X86.Scrub
import VerifiedGarbage.Impl.ChaCha20.X86.Stream
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on x86 -/

namespace VG.Artifacts.ChaCha20.X86

def direct : List (Artifact X86.target) := [
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Fn.init
    verified := Proof.ChaCha20.X86.Scrub.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Fn.setNonce
    verified := Proof.ChaCha20.X86.Scrub.setNonce_scrubbed } ]

public def artifacts : List (Artifact X86.target) :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86.variants.flatMap fun (v : Proof.ChaCha20.X86.XorImpl) => [
    Spec.ChaCha20.applyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20.X86.Fn.apply v.callee
      verified := Proof.ChaCha20.X86.Scrub.apply_scrubbed v
      spSafe := Proof.ChaCha20.X86.Scrub.apply_spSafe v }])

spec_apis artifacts

end VG.Artifacts.ChaCha20.X86
