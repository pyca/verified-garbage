module

public import VerifiedGarbage.Proof.ChaCha20.X86.Scrub
public import VerifiedGarbage.Impl.ChaCha20.X86.Stream
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86

/-! # ChaCha20 (RFC 8439) on x86 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Fn.init
    verified := .scrubbed Proof.ChaCha20.X86.Scrub.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Fn.setNonce
    verified := .scrubbed Proof.ChaCha20.X86.Scrub.setNonce_scrubbed } ]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86.variants.flatMap fun (v : Proof.ChaCha20.X86.XorImpl) => [
    Spec.ChaCha20.applyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20.X86.Fn.apply v.callee
      verified := .scrubbed (Proof.ChaCha20.X86.Scrub.apply_scrubbed v)
      spSafe := Proof.ChaCha20.X86.Scrub.apply_spSafe v }])

end VG.Artifacts.ChaCha20.X86
