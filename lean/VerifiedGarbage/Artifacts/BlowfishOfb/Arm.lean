module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Blowfish.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Blowfish.Arm.FbFinal

/-! # Blowfish-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofb
    stack := 320
    verified := Proof.Blowfish.Arm.ofb_framed },
  Spec.Blowfish.ofbFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofbFinal
    stack := 320
    verified := Proof.Blowfish.Arm.ofbFinal_framed }]

end VG.Artifacts.BlowfishOfb.Arm
