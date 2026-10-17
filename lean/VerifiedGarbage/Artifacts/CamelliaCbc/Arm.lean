module

public import VerifiedGarbage.Proof.Camellia.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_camellia_ecb_encrypt` (bitsliced, in a batch of eight) on each block with the number of rounds, in a 72-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcEncryptChained
    stack := 2904
    verified := Proof.Camellia.Arm.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_camellia_ecb_decrypt` (bitsliced, in a batch of eight) on each block in place with the number of rounds, with the chaining value in a 72-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained
    stack := 2904
    verified := Proof.Camellia.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.Arm
