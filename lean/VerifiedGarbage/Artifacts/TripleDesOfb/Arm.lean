module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on ARMv7 -/

namespace VG.Artifacts.TripleDesOfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.TripleDes.ofbApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ofb
    verified := Proof.TripleDes.Arm.Fn.ofb },
  Spec.TripleDes.ofbFinalApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ofbFinal
    verified := Proof.TripleDes.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.Arm
