module

public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
public import VerifiedGarbage.Proof.Sm4.Arm.EcbAny
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4.Arm

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey
    verified := Proof.Sm4.Arm.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.ecbCall .encrypt
    verified := Proof.Sm4.Arm.ecbCall_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.ecbCall .decrypt
    verified := Proof.Sm4.Arm.ecbCall_verified .decrypt }]

end VG.Artifacts.Sm4.Arm
