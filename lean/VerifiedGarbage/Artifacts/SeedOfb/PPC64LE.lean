module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofb
    stack := 1184
    verified := Proof.Seed.PPC64LE.ofb_framed Proof.Seed.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.SeedOfb.PPC64LE
