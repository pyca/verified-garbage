import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified

/-! # Camellia-CBC artifacts on baseline AArch64 -/

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  { Spec.Camellia.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Camellia.cbcEncryptApi.doc
      (notes := ["Baseline AArch64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/AArch64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cbcEncrypt
    contract := Spec.Camellia.cbcEncryptContract AArch64.abi 3248
    stack := 3248
    verified := Proof.Camellia.AArch64.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Camellia.cbcDecryptApi.doc
      (notes := ["Baseline AArch64: eight blocks at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/AArch64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cbcDecrypt
    contract := Spec.Camellia.cbcDecryptContract AArch64.abi 3248
    stack := 3248
    verified := Proof.Camellia.AArch64.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaCbc.AArch64
