import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified

/-! # Triple DES-CBC artifacts on baseline ARMv7 -/

namespace VG.Artifacts.TripleDesCbc.Arm

def artifacts : List Artifact := [
  { Spec.TripleDes.cbcEncryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_triple_des_ecb_encrypt` on each block in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncrypt
    contract := Spec.TripleDes.cbcEncryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cbcDecryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_triple_des_ecb_decrypt` on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcDecrypt
    contract := Spec.TripleDes.cbcDecryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCbc.Arm
