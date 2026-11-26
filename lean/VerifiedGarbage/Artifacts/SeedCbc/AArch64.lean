module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Impl.Seed.AArch64.Fn
import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on AArch64 -/

namespace VG.Artifacts.SeedCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cbcEncryptChained
    verified := Proof.Seed.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cbcDecryptChained
    verified := Proof.Seed.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.AArch64
