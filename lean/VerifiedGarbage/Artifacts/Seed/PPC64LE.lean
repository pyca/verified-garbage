module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on PPC64LE -/

namespace VG.Artifacts.Seed.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.expandKey
    verified := Proof.Seed.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Seed.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Seed.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Seed.PPC64LE
