module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.Arm

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: prepare the bitsliced round keys once, then encrypt each feedback block in order. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCfb.encrypt
    stack := 1520
    verified := Proof.Sm4.Arm.SerialCfbVerified.framed },
  Spec.Sm4.cfbDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: prepare the bitsliced round keys once and decrypt up to eight ciphertext blocks per batch. The IV and preceding ciphertext blocks are encrypted independently. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCfb.decrypt
    stack := 1520
    verified := Proof.Sm4.Arm.CfbBatchVerified.framed }]

end VG.Artifacts.Sm4Cfb.Arm
