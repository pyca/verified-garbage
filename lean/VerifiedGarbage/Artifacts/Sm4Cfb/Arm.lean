module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Sm4.Arm.FbFinal
public import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.Arm

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCfb.encrypt
    stack := 1520
    verified := Proof.Sm4.Arm.SerialCfbVerified.framed },
  Spec.Sm4.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCfb.decrypt
    stack := 1520
    verified := Proof.Sm4.Arm.CfbBatchVerified.framed },
  Spec.Sm4.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncryptFinal
    stack := 1560
    verified := Proof.Sm4.Arm.cfbEncryptFinal_framed },
  Spec.Sm4.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecryptFinal
    stack := 1560
    verified := Proof.Sm4.Arm.cfbDecryptFinal_framed }]

end VG.Artifacts.Sm4Cfb.Arm
