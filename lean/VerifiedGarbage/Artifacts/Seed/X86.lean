module

public import VerifiedGarbage.Proof.Seed.X86.Scrub
public import VerifiedGarbage.Impl.Seed.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.Lit

/-! # SEED on x86 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.expandKey
    verified := Proof.Seed.X86.Scrub.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.ecb .encrypt
    verified := Proof.Seed.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.ecb .decrypt
    verified := Proof.Seed.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Seed.X86
