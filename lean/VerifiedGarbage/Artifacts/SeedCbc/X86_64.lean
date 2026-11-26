module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Impl.Seed.X86_64.Fn
import VerifiedGarbage.Proof.Seed.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on x86-64 -/

namespace VG.Artifacts.SeedCbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cbcEncrypt, verified := Proof.Seed.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Seed.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cbcDecrypt, verified := Proof.Seed.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cbcDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.X86_64
