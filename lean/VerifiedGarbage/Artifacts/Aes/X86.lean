module

public import VerifiedGarbage.Impl.Aes.X86.Fn
public import VerifiedGarbage.Proof.Aes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # AES (FIPS 197) on x86 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86.target {
    code := Impl.Aes.X86.Fn.expandKey
    verified := Proof.Aes.X86.Scrub.scalar_scrubbed },
  Spec.Aes.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Aes.X86.Fn.expandKeyAesni
    verified := Proof.Aes.X86.Scrub.aesni_scrubbed }]

end VG.Artifacts.Aes.X86
