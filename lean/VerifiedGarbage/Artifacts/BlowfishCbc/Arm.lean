module

public import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_blowfish_ecb_encrypt` on each block in a 56-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcEncryptChained
    stack := 320
    verified := Proof.Blowfish.Arm.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_blowfish_ecb_decrypt` on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcDecryptChained
    stack := 320
    verified := Proof.Blowfish.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.Arm
