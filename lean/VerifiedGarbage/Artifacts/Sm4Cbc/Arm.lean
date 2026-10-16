module

public import VerifiedGarbage.Proof.Sm4.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.Arm

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_sm4_ecb_encrypt` on each block in a 72-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cbcEncrypt
    stack := 1560
    verified := Proof.Sm4.Arm.cbcEncrypt_framed },
  Spec.Sm4.cbcDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_sm4_ecb_decrypt` on each block in place, with the chaining value in a 72-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cbcDecrypt
    stack := 1560
    verified := Proof.Sm4.Arm.cbcDecrypt_framed }]

end VG.Artifacts.Sm4Cbc.Arm
