module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Impl.Seed.AArch64.Fn
import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on AArch64 -/

namespace VG.Artifacts.SeedOfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Seed.ofbApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ofb
    verified := Proof.Seed.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Seed.ofbFinalApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ofbFinal
    verified := Proof.Seed.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.AArch64
