module

public import VerifiedGarbage.Proof.Cast5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # CAST5-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.Arm

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ofb
    verified := .scrubbed Proof.Cast5.Arm.Fn.ofb },
  Spec.Cast5.ofbFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ofbFinal
    verified := .scrubbed Proof.Cast5.Arm.Fn.ofbFinal }]

end VG.Artifacts.Cast5Ofb.Arm
