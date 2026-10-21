module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CbcBatchVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.Arm

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: prepare the bitsliced round keys once, then encrypt each block along the serial CBC feedback chain. The last ciphertext becomes the continuation IV. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCbc.encrypt
    stack := 1520
    verified := Proof.Sm4.Arm.SerialCbcVerified.framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: prepare decryption round keys once, decrypt up to eight ciphertext blocks independently, and XOR with preceding ciphertext in reverse order before it is overwritten. The last ciphertext is retained for continuation. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCbc.decrypt
    stack := 1520
    verified := Proof.Sm4.Arm.CbcBatchVerified.framed }]

end VG.Artifacts.Sm4Cbc.Arm
