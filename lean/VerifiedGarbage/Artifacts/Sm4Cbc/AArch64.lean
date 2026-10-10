import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified

/-! # SM4-CBC artifacts on baseline AArch64 -/

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  { Spec.Sm4.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Sm4.cbcEncryptApi.doc
      (notes := ["Baseline AArch64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/AArch64/`, over SM4's ECB core."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.cbcEncrypt
    contract := Spec.Sm4.cbcEncryptContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Sm4.cbcDecryptApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/AArch64/`, over SM4's ECB core."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.cbcDecrypt
    contract := Spec.Sm4.cbcDecryptContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Cbc.AArch64
