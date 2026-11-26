module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Proof.Seed.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on ARMv7 -/

namespace VG.Artifacts.SeedOfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Seed.ofbApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofb
    verified := Proof.Seed.Arm.Fn.ofb },
  Spec.Seed.ofbFinalApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ofbFinal
    verified := Proof.Seed.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.Arm
