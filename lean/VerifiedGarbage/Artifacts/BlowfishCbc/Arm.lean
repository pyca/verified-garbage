module

public import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_blowfish_ecb_encrypt` on each block in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcEncrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cbcEncrypt_framed },
  Spec.Blowfish.cbcDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_blowfish_ecb_decrypt` on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcDecrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cbcDecrypt_framed }]

end VG.Artifacts.BlowfishCbc.Arm
