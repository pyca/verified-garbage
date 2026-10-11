import VerifiedGarbage.Proof.Sm4.Arm.CbcVerified

/-! # SM4-CBC artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Sm4Cbc.Arm

def artifacts : List Artifact := [
  { Spec.Sm4.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Sm4.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_sm4_ecb_encrypt` on each block in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cbcEncrypt
    contract := Spec.Sm4.cbcEncryptContract Arm.abi 1536
    stack := 1536
    verified := Proof.Sm4.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Sm4.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_sm4_ecb_decrypt` on each block in place, with the chaining value in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cbcDecrypt
    contract := Spec.Sm4.cbcDecryptContract Arm.abi 1536
    stack := 1536
    verified := Proof.Sm4.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Cbc.Arm
