module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on PPC64LE -/

namespace VG.Artifacts.SeedCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Seed.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Seed.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.PPC64LE
