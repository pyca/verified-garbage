module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Cast5.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Cast5.Arm.FbFinal

/-! # CAST5-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.Arm

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.ofb
    stack := 336
    verified := Proof.Cast5.ofb_keyed Proof.Cast5.Arm.ofb_framed },
  Spec.Cast5.ofbFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.ofbFinal
    stack := 336
    verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.Arm.ofbFinal_framed }]

end VG.Artifacts.Cast5Ofb.Arm
