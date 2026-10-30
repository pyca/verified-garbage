module

public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.Arm

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb
    stack := 832
    verified := Proof.Seed.Arm.ofb_framed }]

end VG.Artifacts.SeedOfb.Arm
