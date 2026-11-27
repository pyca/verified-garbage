module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on PPC64LE -/

namespace VG.Artifacts.SeedCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Seed.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Seed.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Seed.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Seed.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Seed.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCfb.PPC64LE
