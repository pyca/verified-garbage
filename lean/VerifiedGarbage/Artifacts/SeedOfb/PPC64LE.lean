module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on PPC64LE -/

namespace VG.Artifacts.SeedOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Seed.ofbApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ofb
    verified := Proof.Seed.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ofbFinal
    verified := Proof.Seed.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.PPC64LE
