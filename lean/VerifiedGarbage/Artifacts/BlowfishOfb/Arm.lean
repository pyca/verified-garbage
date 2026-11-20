module

public import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ofb
    verified := .scrubbed Proof.Blowfish.Arm.Fn.ofb },
  Spec.Blowfish.ofbFinalApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ofbFinal
    verified := .scrubbed Proof.Blowfish.Arm.Fn.ofbFinal }]

end VG.Artifacts.BlowfishOfb.Arm
