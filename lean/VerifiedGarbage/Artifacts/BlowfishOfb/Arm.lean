module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on ARMv7 -/

namespace VG.Artifacts.BlowfishOfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Blowfish.ofbApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ofb
    verified := Proof.Blowfish.Arm.Fn.ofb },
  Spec.Blowfish.ofbFinalApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ofbFinal
    verified := Proof.Blowfish.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.Arm
