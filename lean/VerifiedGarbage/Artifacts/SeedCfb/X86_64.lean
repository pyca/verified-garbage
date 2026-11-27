module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Impl.Seed.X86_64.Fn
import VerifiedGarbage.Proof.Seed.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on x86-64 -/

namespace VG.Artifacts.SeedCfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Seed.cfbEncryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbEncrypt, verified := Proof.Seed.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Seed.cfbDecryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbDecrypt, verified := Proof.Seed.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Seed.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbEncryptFinal, verified := Proof.Seed.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Seed.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbDecryptFinal, verified := Proof.Seed.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.SeedCfb.X86_64
