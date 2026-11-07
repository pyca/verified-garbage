module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Sm4.Arm.FbFinal

/-! # SM4-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialOfb.crypt
    stack := 1520
    verified := Proof.Sm4.Arm.SerialOfbVerified.framed },
  Spec.Sm4.ofbFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofbFinal
    stack := 1560
    verified := Proof.Sm4.Arm.ofbFinal_framed }]

end VG.Artifacts.Sm4Ofb.Arm
