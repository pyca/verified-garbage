module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Impl.Seed.X86_64.Fn
import VerifiedGarbage.Proof.Seed.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on x86-64 -/

namespace VG.Artifacts.Seed.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Seed.expandKeyApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.expandKey, verified := Proof.Seed.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.expandKey_spSafe },
  Spec.Seed.ecbEncryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ecbEncrypt, verified := Proof.Seed.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Seed.ecbDecryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ecbDecrypt, verified := Proof.Seed.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ecbDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Seed.X86_64
