module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512VL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86_64
import VerifiedGarbage.Proof.ChaCha20.X86_64.Scrub
import VerifiedGarbage.Proof.ChaCha20.X86_64.ScrubInit
import VerifiedGarbage.Impl.ChaCha20.X86_64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on x86-64 -/

namespace VG.Artifacts.ChaCha20.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.ChaCha20.initApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Fn.init
    verified := Proof.ChaCha20.X86_64.Scrub.init_scrubbed
    spSafe := Proof.ChaCha20.X86_64.Scrub.init_spSafeFn },
  Spec.ChaCha20.setNonceApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Fn.setNonce
    verified := Proof.ChaCha20.X86_64.Scrub.setNonce_scrubbed
    spSafe := Proof.ChaCha20.X86_64.Scrub.setNonce_spSafeFn }]

public def artifacts : List (Artifact X86_64.target) :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86_64.xorVariants.map fun (v : Proof.ChaCha20.X86_64.XorImpl) =>
    Spec.ChaCha20.applyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.ChaCha20.X86_64.Fn.apply v.level v.callee
      verified := Proof.ChaCha20.X86_64.Scrub.apply_scrubbed v
      spSafe := Proof.ChaCha20.X86_64.Scrub.apply_spSafeFn v })

spec_apis artifacts

end VG.Artifacts.ChaCha20.X86_64
