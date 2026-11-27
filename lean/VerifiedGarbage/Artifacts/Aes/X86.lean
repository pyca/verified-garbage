module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Impl.Aes.X86.Fn
import VerifiedGarbage.Proof.Aes.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES (FIPS 197) on x86 -/

namespace VG.Artifacts.Aes.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Aes.expandKeyApi.artifact X86.target {
    code := Impl.Aes.X86.Fn.expandKey
    verified := Proof.Aes.X86.Scrub.scalar_scrubbed },
  Spec.Aes.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Aes.X86.Fn.expandKeyAesni
    verified := Proof.Aes.X86.Scrub.aesni_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Aes.X86
