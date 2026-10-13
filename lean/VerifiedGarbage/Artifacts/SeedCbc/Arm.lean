module

public import VerifiedGarbage.Proof.Seed.Arm.CbcVerified
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # SEED-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.Arm

def artifacts : List Artifact := [
  { Spec.Seed.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Seed.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_seed_ecb_encrypt` on each block in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncrypt
    contract := Spec.Seed.cbcEncryptContract Arm.abi 832
    stack := 832
    verified := Proof.Seed.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Seed.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_seed_ecb_decrypt` on each block in place, with the chaining value in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecrypt
    contract := Spec.Seed.cbcDecryptContract Arm.abi 832
    stack := 832
    verified := Proof.Seed.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.SeedCbc.Arm
