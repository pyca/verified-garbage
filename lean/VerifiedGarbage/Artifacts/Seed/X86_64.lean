module

public import VerifiedGarbage.Impl.Seed.X86_64.Fn
public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # SEED on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.expandKey, verified := Proof.Seed.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.expandKey_spSafe },
  Spec.Seed.ecbEncryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ecbEncrypt, verified := Proof.Seed.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Seed.ecbDecryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ecbDecrypt, verified := Proof.Seed.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ecbDecrypt_spSafe }]

end VG.Artifacts.Seed.X86_64
