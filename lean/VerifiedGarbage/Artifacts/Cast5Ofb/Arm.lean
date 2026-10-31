module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.Arm

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.ofb
    stack := 336
    verified := Proof.Cast5.Arm.ofb_framed }]

end VG.Artifacts.Cast5Ofb.Arm
