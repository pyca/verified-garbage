module

public import VerifiedGarbage.Proof.Seed.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.Arm

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_seed_ecb_encrypt` on each block in a 72-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained
    stack := 832
    verified := Proof.Seed.Arm.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_seed_ecb_decrypt` on each block in place, with the chaining value in a 72-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained
    stack := 832
    verified := Proof.Seed.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.Arm
