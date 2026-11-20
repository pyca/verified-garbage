module

public import VerifiedGarbage.Proof.Seed.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SEED-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.Arm

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofb
    verified := .scrubbed Proof.Seed.Arm.Fn.ofb },
  Spec.Seed.ofbFinalApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofbFinal
    verified := .scrubbed Proof.Seed.Arm.Fn.ofbFinal }]

end VG.Artifacts.SeedOfb.Arm
