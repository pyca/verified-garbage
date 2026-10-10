import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified

/-! # SM4-CBC artifacts on baseline x86-64 -/

namespace VG.Artifacts.Sm4Cbc.X86_64

def artifacts : List Artifact := [
  { Spec.Sm4.cbcEncryptApi with
    target := X86_64.target
    doc := Spec.Sm4.cbcEncryptApi.doc
      (notes := ["Baseline x86-64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/X86_64/`, over SM4's ECB core."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 Impl.Sm4.X86_64.cbcEncrypt
    contract := Spec.Sm4.cbcEncryptContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sm4.cbcDecryptApi with
    target := X86_64.target
    doc := Spec.Sm4.cbcDecryptApi.doc
      (notes := ["Baseline x86-64: sixteen blocks at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/X86_64/`, over SM4's ECB core."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 Impl.Sm4.X86_64.cbcDecrypt
    contract := Spec.Sm4.cbcDecryptContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sm4Cbc.X86_64
