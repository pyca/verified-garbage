module

public import VerifiedGarbage.Proof.Seed.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # SEED-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Seed.ofbApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofb
    verified := Proof.Seed.Arm.Fn.ofb },
  Spec.Seed.ofbFinalApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofbFinal
    verified := Proof.Seed.Arm.Fn.ofbFinal }]

end VG.Artifacts.SeedOfb.Arm
