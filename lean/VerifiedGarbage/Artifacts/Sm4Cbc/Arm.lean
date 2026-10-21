module

public import VerifiedGarbage.Proof.Sm4.Arm.CbcVerified
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
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
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_sm4_ecb_decrypt` on each block in place, with the chaining value in a 72-byte working space on the stack, zeroed on return; the chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cbcDecryptChained
    stack := 1560
    verified := Proof.Sm4.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.Arm
