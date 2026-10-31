module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.AArch64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofb
    stack := 1456
    verified := Proof.Seed.AArch64.ofb_framed }]

end VG.Artifacts.SeedOfb.AArch64
